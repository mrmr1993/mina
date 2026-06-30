#!/usr/bin/env python3
"""Generate resource-aware scheduler configs for the nori proof conversion.

A config is the complete, reproducible spec of a run:
  { "budget": float,
    "jobs": { <job-key>: alloc } }
where an alloc is either a bare int N (shorthand for {cores:N, cost:N,
priority:0}) or an object {"cores": int, "cost": float, "priority": int,
"worker": str}. cores is the rayon the worker runs the job at; cost is what the
job draws from budget (cores > cost models oversubscription); priority is the
scheduling-order dial (higher runs first among ready, affordable tasks); worker
(base jobs only) pins the job to a worker -- the runner derives the worker set
and each worker's base-circuit shard from these.

Job keys: base circuit index "0".."23", "layer1:<i>", "node:<layer>:<i>", and a
"default" fallback (covers witness/compute-state jobs).

Usage: gen.py <name> > configs/<name>.json
"""
import json
import sys

# Worker shards (het-14 layout): which base circuits each worker compiles/serves.
SHARDS = [[8, 9], [10, 11], [14, 15], [16, 17], [20, 21], [22, 23],
          [0, 1], [2, 3], [4, 5], [6], [7], [12, 13], [18], [19]]
WORKER_OF = {c: f"w{i}" for i, sh in enumerate(SHARDS) for c in sh}

# Priority tiers: witness/compute-state must run first (gate everything), base
# proofs next, merges last. The budget handles contention; priority only breaks
# ties among ready, affordable tasks.
PRI_DEFAULT, PRI_BASE, PRI_MERGE = 3, 2, 0


def _tail(jobs, ramp):
    """Lean disciplined tail (1:1 cost, merge priority). ramp[L] = real node:L cores."""
    for i in range(16):
        jobs[f"layer1:{i}"] = {"cores": 1, "cost": 1, "priority": PRI_MERGE}
    for i in range(8):
        c = ramp[2] if i < 6 else 1
        jobs[f"node:2:{i}"] = {"cores": c, "cost": c, "priority": PRI_MERGE}
    for i in range(4):
        c = ramp[3] if i < 3 else 1
        jobs[f"node:3:{i}"] = {"cores": c, "cost": c, "priority": PRI_MERGE}
    for i in range(2):
        jobs[f"node:4:{i}"] = {"cores": ramp[4], "cost": ramp[4], "priority": PRI_MERGE}
    jobs["node:5:0"] = {"cores": ramp[5], "cost": ramp[5], "priority": PRI_MERGE}
    jobs["default"] = {"cores": 1, "cost": 1, "priority": PRI_DEFAULT}


def oversub_head():
    """Oversubscribed head (5-thread base) + lean disciplined tail.

    Base runs on 5 threads each (like uniform R5, head ~70s with merges held
    off by the budget) but draws only ~1.4 budget so all 14 workers run
    concurrently. The tail stays 1:1 so the 12 layer-1 merges never contend.
    """
    jobs = {}
    for n in range(24):
        jobs[str(n)] = {"cores": 5, "cost": 1.4, "priority": PRI_BASE,
                        "worker": WORKER_OF[n]}
    _tail(jobs, {2: 2, 3: 4, 4: 6, 5: 8})
    return {"budget": 20, "jobs": jobs}


def het():
    """Het oversubscribed head: heavy base (slow witness) get more threads than
    light, and light cost less so the head leaves a little budget headroom for
    early layer-1 merges to overlap. Heavy 5-thread / light 3-thread; head wave
    (6 heavy + 8 light) draws 6*1.5 + 8*1.2 = 18.6, leaving ~1.4 for overlap.
    """
    jobs = {}
    heavy = {8, 9, 10, 11, 14, 15, 16, 17, 20, 21, 22, 23}
    for n in range(24):
        if n in heavy:
            jobs[str(n)] = {"cores": 5, "cost": 1.5, "priority": PRI_BASE,
                            "worker": WORKER_OF[n]}
        else:
            jobs[str(n)] = {"cores": 3, "cost": 1.2, "priority": PRI_BASE,
                            "worker": WORKER_OF[n]}
    _tail(jobs, {2: 2, 3: 4, 4: 6, 5: 8})
    return {"budget": 20, "jobs": jobs}


CONFIGS = {"oversub_head": oversub_head, "het": het}

if __name__ == "__main__":
    name = sys.argv[1] if len(sys.argv) > 1 else "oversub_head"
    print(json.dumps(CONFIGS[name](), indent=1))
