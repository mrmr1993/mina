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
    starts, ends, cmds, rayons = {}, {}, {}, {}
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
                         end=ends[n], rayon=rayons.get(n)))
    return jobs


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
    for j in jobs:
        if j["cls"] != last_cls:
            last_cls = j["cls"]
        s, e = col(j["start"]), max(col(j["start"]) + 1, col(j["end"]))
        bar = " " * s + "#" * (e - s)
        bar = bar[:width].ljust(width)
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    ap.add_argument("--width", type=int, default=110)
    ap.add_argument("--config")
    a = ap.parse_args()
    config = json.load(open(a.config)) if a.config else None
    jobs = parse(a.log)
    if not jobs:
        print("no job events found in log", file=sys.stderr)
        sys.exit(1)
    render(jobs, a.width, config)


if __name__ == "__main__":
    main()
