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
        if row % 2 == 1:
            bar = bar.replace(" ", "-")
        r = f"r{j['rayon']}" if j["rayon"] is not None else "  "
        lbl = f"{j['cls'][:4]:>5} {j['label']:<10} {r:>3}"
        print(f"{lbl[:17]:<17}|{bar}|")
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


def render_workers(jobs, width, config):
    """One row per worker (the actual serving worker.<i>.sock), showing its busy
    timeline so idle gaps to fill are obvious. Each column is the class code of a
    job active on that worker there; '+' marks 2+ overlapping jobs, ' ' is idle."""
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
          f"(b=base s=state w=witness m=merge, +=overlap)")
    print(" " * 18 + "0" + "-" * (width - 1) + f"{span:.0f}s")
    for sock in sorted(by_sock):
        ws = by_sock[sock]
        cells, busy = [], 0.0
        for c in range(width):
            t = t0 + (c + 0.5) / scale
            active = [j for j in ws if j["start"] <= t < j["end"]]
            if not active:
                cells.append(" ")
            elif len(active) > 1:
                cells.append("+")
            else:
                cells.append(CLS_CODE.get(active[0]["cls"], "?"))
        for j in ws:
            busy += min(j["end"], t0 + span) - j["start"]
        util = 100 * busy / span if span > 0 else 0
        name = labels.get(sock, f"sock{sock}")
        print(f"{name:>12} ({len(ws):>2}) |{''.join(cells)}|  {util:.0f}%")


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
