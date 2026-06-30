#!/usr/bin/env python3
"""Generate resource-aware scheduler configs for the nori proof conversion.

A config is { "budget": float, "jobs": { <job-key>: alloc } } where an alloc is
either a bare int N (shorthand for {cores: N, cost: N}, i.e. 1:1, no
oversubscription) or {"cores": int, "cost": float}. cores is the rayon the
worker runs the job at; cost is what the job draws from the budget. cores > cost
models oversubscription.

Job keys are per-job identities: base circuit index "0".."23", "layer1:<i>",
"node:<layer>:<i>", plus a "default" fallback.

Usage: gen.py <name> > configs/<name>.json
"""
import json
import sys

# Tree shape for 24 base proofs padded to 32: layer1 has 16 nodes (12 real +
# 4 padding), node:2 has 8 (6+2), node:3 has 4 (3+1), node:4 has 2, node:5 has 1.
HEAVY_BASE = {8, 9, 10, 11, 14, 15, 16, 17, 20, 21, 22, 23}


def _tail(jobs, ramp):
    """Lean disciplined tail (1:1 cost). ramp[L] = cores for real node:L nodes."""
    for i in range(16):
        jobs[f"layer1:{i}"] = 1
    for i in range(6):
        jobs[f"node:2:{i}"] = ramp[2]
    for i in (6, 7):
        jobs[f"node:2:{i}"] = 1
    for i in range(3):
        jobs[f"node:3:{i}"] = ramp[3]
    jobs["node:3:3"] = 1
    for i in range(2):
        jobs[f"node:4:{i}"] = ramp[4]
    jobs["node:5:0"] = ramp[5]
    jobs["default"] = 1


def oversub_head():
    """Oversubscribed head (R5-style 5-thread base) + lean disciplined tail.

    Base runs on 5 threads each (like uniform R5, head ~82s) but only draws
    20/14 ~= 1.4 budget so all 14 workers run concurrently. The tail stays 1:1
    so the 12 layer-1 merges (1 core each) never contend.
    """
    jobs = {}
    for n in range(24):
        jobs[str(n)] = {"cores": 5, "cost": 1.4}
    _tail(jobs, {2: 2, 3: 4, 4: 6, 5: 8})
    return {"budget": 20, "jobs": jobs}


CONFIGS = {"oversub_head": oversub_head}

if __name__ == "__main__":
    name = sys.argv[1] if len(sys.argv) > 1 else "oversub_head"
    print(json.dumps(CONFIGS[name](), indent=1))
