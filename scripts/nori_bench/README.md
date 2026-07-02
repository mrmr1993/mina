# nori_bench — resource-aware runner for SP1→Plonk proof conversion

Runs a full nori proof conversion (24 base proofs → binary compression tree →
root) under a **resource-aware scheduler** whose behaviour is fully specified by
a single JSON config. One config = one reproducible run: worker set, per-job
`{cores, cost, priority, worker}`, and the global budget.

## Quick start

```bash
# build the converter first (from the repo root)
dune build src/app/proof_conversion/nori_proof_converter.exe

# run the canonical config
scripts/nori_bench/run.sh scripts/nori_bench/configs/het86.json
```

`run.sh` prints the makespan / VK-match line, e.g.

```
==> [het86] makespan=101  cores=17.2  peak=19.46GB  minAvail=4059MB  vk=true  oom=false
```

and an ASCII Gantt of the run. It also writes the timing log to
`/tmp/nori_run_<name>.dag.log`; re-render it (and a per-worker view) with:

```bash
python3 scripts/nori_bench/gantt.py /tmp/nori_run_het86.dag.log \
    --config scripts/nori_bench/configs/het86.json --by-worker
```

`het86.json` is the reference config that reaches ~101s (single proof, CPU-only,
VK-preserving) on a 20-core host. It is **tuned to that machine** — worker count,
oversubscription, and budget are host-specific; retune for other hardware (see
below).

## What the run needs

`run.sh` / `bench.sh` set the required environment automatically:
`KIMCHI_FUSED_EVAL=1`, `MINA_USE_MMAP_CACHE=1`, `MALLOC_ARENA_MAX=2`,
`OCAMLRUNPARAM='O=20'`, plus per-task `KIMCHI_PROVE_THREADS` (from the config's
`--rayon`). These activate the proof-systems prover optimisations the result
depends on. Set `KIMCHI_FUSED_EVAL=0` to A/B the fused evaluator.

## Config schema

```json
{
  "budget": 20,
  "jobs": {
    "0":          { "cores": 4, "cost": 2, "priority": 2, "worker": "w0" },
    "layer1:5":   { "cores": 2, "cost": 2, "priority": 0, "worker": "w11" },
    "node:3:0":   { "cores": 6, "cost": 5, "priority": 0, "worker": "w0" },
    "state:8":    { "cores": 1, "cost": 0, "priority": 3, "worker": "w13" },
    "aux-witness":{ "cores": 1, "cost": 0, "priority": 3, "worker": "w12" },
    "default":    { "cores": 1, "cost": 1, "priority": 0 }
  }
}
```

- **Job keys:** base circuit index `"0".."23"`; `"layer1:<i>"` and
  `"node:<layer>:<i>"` merges; `"state:<n>"` compute-state; `"aux-witness"`; and
  a `"default"` fallback. A bare integer `N` is shorthand for
  `{cores:N, cost:N, priority:0}`.
- **cores** — rayon threads the worker runs the job at (`--rayon`, →
  `KIMCHI_PROVE_THREADS`). `cores > cost` models oversubscription.
- **cost** — budget the job draws; a job dispatches only when the free budget
  covers it. `cost:0` = never blocks (used for cheap state/witness jobs).
- **priority** — orders *ready* jobs (higher first). State/witness high, base
  mid, merges low.
- **worker** — pins the job to a named worker. `run.sh` derives the worker set
  and each worker's base-circuit shard from the `worker` fields; every base
  circuit `0..23` must be assigned to some worker or the run aborts.

## Tuning for other hardware

Each worker is a persistent proving process; `cores`/`cost`/`budget` set how many
run concurrently and how hard each is oversubscribed. The wins that reached
~101s: free the critical-path worker early (give its base circuit more cores),
co-locate the serial `state:8–11` chain on one worker, and widen the deep merge
tail (`node:3/4/5`) once RAM is free. `configs/gen.py` generates starting configs
programmatically. Watch `minAvail` — oversubscription that dips below ~1–2 GB
risks OOM.

## Files

- `run.sh` — the entry point: `run.sh CONFIG.json`.
- `gantt.py` — ASCII Gantt (per-job + `--by-worker`) from a DAG log.
- `bench.sh` — lower-level harness `run.sh` calls (worker startup, env, timing).
- `configs/` — `het86.json` (canonical) + `gen.py` (config generator).
