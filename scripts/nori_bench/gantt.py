#!/usr/bin/env python3
"""Render an ASCII Gantt chart from a nori proof-conversion DAG log.

The converter's run_dag logs timestamped task events:
  [<unix>] #<n> starting [..] rayon=<r> $ <dispatch-wrapped inner cmd>
  [<unix>] #<n> completed [..] $ <inner cmd>

This reads those, reconstructs each job's [start, end] and rayon, and draws a
time-scaled Gantt grouped by job class, with a per-second core-utilisation strip
at the bottom. Lets you see the head/tail shape, overlaps and idle gaps directly
rather than trusting a summary number.

Usage: gantt.py <dag-log> [--width N] [--config config.json]
"""
import argparse
import json
import re
import sys


def job_key(cmd):
    parts = cmd.split()
    if not parts:
        return None
    if parts[0] == "prove-zkp":
        return ("base", parts[2])
    if parts[0] == "compress":
        _, _, _bc, layer, index = parts[:5]
        return ("merge", f"layer1:{index}" if layer == "1" else f"node:{layer}:{index}")
    if parts[0] == "compute-state":
        return ("state", parts[2])
    if "generate-witness" in cmd:
        return ("witness", "gw")
    if "aux-witness" in cmd:
        return ("witness", "aux")
    return ("other", parts[0])


def parse(path):
    starts, ends, cmds, rayons, sockets = {}, {}, {}, {}, {}
    for ln in open(path, errors="ignore"):
        m = re.search(r"\[(\d+\.\d+)\] #(\d+) (starting|completed)", ln)
        if not m:
            continue
        t, n, kind = float(m.group(1)), int(m.group(2)), m.group(3)
        if kind == "starting":
            starts.setdefault(n, t)
            rm = re.search(r"rayon=(\d+)", ln)
            if rm:
                rayons[n] = int(rm.group(1))
            sm = re.search(r"worker\.(\d+)\.sock", ln)
            if sm:
                sockets[n] = int(sm.group(1))
        else:
            cm = re.search(r"\$ (.+)", ln)
            cmds[n] = cm.group(1).strip() if cm else ""
            ends[n] = t
    jobs = []
    for n in ends:
        if n not in starts:
            continue
        k = job_key(cmds[n])
        if k is None:
            continue
        jobs.append(dict(n=n, cls=k[0], label=k[1], start=starts[n],
                         end=ends[n], rayon=rayons.get(n), socket=sockets.get(n)))
    return jobs


def slot_labels(config):
    """Reproduce run.sh's socket-slot -> worker-label mapping: workers are sorted
    by their (string) label, and worker.<i>.sock is the i-th in that order."""
    if not config:
        return None
    labels = sorted({v["worker"] for v in config.get("jobs", {}).values()
                     if isinstance(v, dict) and "worker" in v})
    return {i: lbl for i, lbl in enumerate(labels)}


# class display order + a single-letter code
ORDER = ["witness", "state", "base", "merge", "other"]


def cost_lookup(config):
    if not config:
        return None
    jobs = config.get("jobs", {})

    def cost(cls, label):
        key = label if cls in ("base", "merge") else "default"
        a = jobs.get(key, jobs.get("default", 1))
        if isinstance(a, dict):
            return float(a.get("cost", a.get("cores", 1)))
        return float(a)
    return cost


def render(jobs, width, config):
    t0 = min(j["start"] for j in jobs)
    span = max(j["end"] for j in jobs) - t0
    scale = width / span if span > 0 else 1.0

    def col(t):
        return int((t - t0) * scale)

    jobs.sort(key=lambda j: (ORDER.index(j["cls"]) if j["cls"] in ORDER else 9,
                             j["start"]))
    print(f"makespan {span:.0f}s   {len(jobs)} jobs   1 col ~= {1/scale:.1f}s   "
          f"(r = rayon)")
    print(" " * 18 + "0" + "-" * (width - 1) + f"{span:.0f}s")
    last_cls = None
    for row, j in enumerate(jobs):
        if j["cls"] != last_cls:
            last_cls = j["cls"]
        s, e = col(j["start"]), max(col(j["start"]) + 1, col(j["end"]))
        bar = " " * s + "#" * (e - s)
        bar = bar[:width].ljust(width)
        r = f"r{j['rayon']}" if j["rayon"] is not None else "  "
        lbl = f"{j['cls'][:4]:>5} {j['label']:<10} {r:>3}"
        cell = f"{lbl[:17]:<17}"
        if row % 2 == 1:
            bar = bar.replace(" ", "-")
            cell = cell.rstrip() + "-" * (len(cell) - len(cell.rstrip()))
        print(f"{cell}|{bar}|")
    # utilisation strips, sampled instantaneously at each column midpoint and
    # normalised to the budget (full bar = budget; rayon over budget = saturated)
    print("-" * (18 + width))
    budget = float((config or {}).get("budget", 0)) or max(
        (j["rayon"] or 0) for j in jobs)
    cost = cost_lookup(config)
    strips = [("rayon", lambda j: j["rayon"] or 0)]
    if cost:
        strips.append(("cost", lambda j: cost(j["cls"], j["label"])))
    for metric, get in strips:
        row = [
            sum(get(j) for j in jobs
                if j["start"] <= t0 + (c + 0.5) / scale < j["end"])
            for c in range(width)
        ]
        spark = "".join(
            " .:-=+*#%@"[min(9, int(v / (budget or 1) * 9))] for v in row)
        print(f"{metric+' sum':>16} |{spark}|  peak={max(row):.0f}"
              f"  (full bar = budget {budget:.0f})")


CLS_CODE = {"witness": "w", "state": "s", "base": "b", "merge": "m", "other": "?"}


# merge nodes get a flat global id numbered layer-by-layer (layer1 first):
# layer1:i -> i (0..15), node:2:i -> 16+i, node:3:i -> 24+i, node:4:i -> 28+i,
# node:5:0 -> 30. Counts assume the 32-leaf padded tree.
_LAYER_COUNTS = [16, 8, 4, 2, 1]
_LAYER_OFFSET = {}
_acc = 0
for _L, _c in enumerate(_LAYER_COUNTS, start=1):
    _LAYER_OFFSET[_L] = _acc
    _acc += _c


def merge_node_id(label):
    if label.startswith("layer1:"):
        layer, idx = 1, int(label.split(":")[1])
    else:  # node:<layer>:<idx>
        _, layer, idx = label.split(":")
        layer, idx = int(layer), int(idx)
    return _LAYER_OFFSET.get(layer, 0) + idx


def job_short_id(j):
    """Compact per-job label to show inside its bar segment: merge -> node id,
    base -> circuit index, state -> sN, witness -> its short tag."""
    cls, label = j["cls"], j["label"]
    if cls == "merge":
        return str(merge_node_id(label))
    if cls == "state":
        return "s" + label
    if cls == "base":
        return label
    if cls == "witness":
        return label
    return "?"


def render_workers(jobs, width, config):
    """Two rows per worker (the actual serving worker.<i>.sock): an id row
    showing each job's id centred in its segment (merge=node id, base=circuit
    index, sN=state), and a class row (b/s/w/m). '|' marks segment boundaries,
    '+' marks 2+ overlapping jobs, ' ' is idle. Makes idle gaps and which job
    holds each slot obvious at a glance."""
    served = [j for j in jobs if j.get("socket") is not None]
    if not served:
        print("(no worker-socket info in log -- cannot draw per-worker view)")
        return
    t0 = min(j["start"] for j in served)
    span = max(j["end"] for j in served) - t0
    scale = width / span if span > 0 else 1.0
    labels = slot_labels(config) or {}
    by_sock = {}
    for j in served:
        by_sock.setdefault(j["socket"], []).append(j)
    print()
    print(f"per-worker  makespan {span:.0f}s   1 col ~= {1/scale:.1f}s   "
          f"(ids: merge=node base=circuit sN=state; b/s/w/m=class; +=overlap)")
    print(" " * 18 + "0" + "-" * (width - 1) + f"{span:.0f}s")

    def sort_key(sock):
        m = re.search(r"\d+", labels.get(sock, ""))
        return (int(m.group()) if m else sock)

    for sock in sorted(by_sock, key=sort_key):
        ws = by_sock[sock]
        active, cls = [], []
        for c in range(width):
            t = t0 + (c + 0.5) / scale
            hits = [j for j in ws if j["start"] <= t < j["end"]]
            if len(hits) > 1:
                active.append("+")
                cls.append("+")
            elif hits:
                active.append(hits[0]["n"])
                cls.append(CLS_CODE.get(hits[0]["cls"], "?"))
            else:
                active.append(None)
                cls.append(" ")
        id_row = [" " if a is None else "+" if a == "+" else "-" for a in active]
        ids = {j["n"]: job_short_id(j) for j in ws}
        c = 0
        while c < width:
            a = active[c]
            if a is None or a == "+":
                c += 1
                continue
            start = c
            while c < width and active[c] == a:
                c += 1
            # boundary marker at the segment start (both rows aligned)
            id_row[start], cls[start] = "|", "|"
            seg = c - start - 1
            lbl = ids.get(a, "")[:max(seg, 0)]
            off = start + 1 + (seg - len(lbl)) // 2
            for i, ch in enumerate(lbl):
                id_row[off + i] = ch
        busy = sum(min(j["end"], t0 + span) - j["start"] for j in ws)
        util = 100 * busy / span if span > 0 else 0
        name = labels.get(sock, f"sock{sock}")
        print(f"{name:>11} ({len(ws):>2}) |{''.join(id_row)}|  {util:.0f}%")
        print(f"{'':>16} |{''.join(cls)}|")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    ap.add_argument("--width", type=int, default=110)
    ap.add_argument("--config")
    ap.add_argument("--by-worker", action="store_true",
                    help="also draw a per-worker utilisation Gantt")
    ap.add_argument("--workers-only", action="store_true",
                    help="draw only the per-worker Gantt")
    a = ap.parse_args()
    config = json.load(open(a.config)) if a.config else None
    jobs = parse(a.log)
    if not jobs:
        print("no job events found in log", file=sys.stderr)
        sys.exit(1)
    if not a.workers_only:
        render(jobs, a.width, config)
    if a.by_worker or a.workers_only:
        render_workers(jobs, a.width, config)


if __name__ == "__main__":
    main()
