# Reproducing the nori SP1→Plonk conversion result

This directory reproduces a full **SP1→Plonk proof conversion** (24 base proofs →
binary compression tree → single root) under a resource-aware scheduler. On a
20-core host it completes in **~101 s, single proof, CPU-only, VK-preserving**
(`vk=true`). This README is the standalone reproduction guide for reviewers,
ahead of the split-out PR series.

## What makes up the result

Three layers, all on this branch:

1. **proof-systems (Rust submodule)** — a stack of prover optimisations the
   result depends on: a fused row-wise constraint evaluator (`KIMCHI_FUSED_EVAL`),
   d1-row skipping in the quotient, peak-RAM/parallelisation work, lookup
   subsampling, a warm per-task rayon pool (`KIMCHI_PROVE_THREADS`), and the fat
   prover (oracle-skip). The submodule is pinned to exactly this stack — no
   unused/experimental commits.
2. **OCaml converter + scheduler** (`src/app/proof_conversion/`) — the converter
   plus a config-driven resource-aware scheduler.
3. **This runner** — `run.sh` drives one conversion from a single JSON config and
   sets the required environment.

## Prerequisites

- The Mina build toolchain (opam switch per the repo root README) and a Rust
  toolchain for the proof-systems submodule.
- Submodules initialised: `git submodule update --init --recursive`.
- A ~20-core host with **≥24 GB RAM** — the reference config oversubscribes and
  peaks around 20–22 GB; less headroom risks OOM (watch `minAvail`).

## Build

```bash
git submodule update --init --recursive
dune build src/app/proof_conversion/nori_proof_converter.exe
```

## Run

```bash
scripts/nori_bench/run.sh scripts/nori_bench/configs/het86.json
```

Expected tail (numbers vary ±1–2 s by host load):

```
==> [het86] makespan=101  cores=17.2  peak=19.46GB  minAvail=4059MB  vk=true  oom=false
```

`makespan` is the wall-clock seconds for the single conversion; `vk=true` is the
VK-match check (the whole point — the optimised path yields the identical
verification key). The run also writes a timing log to
`/tmp/nori_run_het86.dag.log`; render a Gantt (per-job and per-worker) with:

```bash
python3 scripts/nori_bench/gantt.py /tmp/nori_run_het86.dag.log \
    --config scripts/nori_bench/configs/het86.json --by-worker
```

## Environment (set automatically by the runner)

`run.sh`/`bench.sh` export what the prover stack needs — no manual setup:
`KIMCHI_FUSED_EVAL=1`, `MINA_USE_MMAP_CACHE=1`, `MALLOC_ARENA_MAX=2`,
`OCAMLRUNPARAM='O=20'`, and per-task `KIMCHI_PROVE_THREADS` (from the config's
`--rayon`). Set `KIMCHI_FUSED_EVAL=0` to A/B the fused evaluator.

## The config

`configs/het86.json` is the reference config that reaches ~101 s. It is **tuned
to a 20-core host** — worker count, oversubscription, and budget are
host-specific. `run.sh CONFIG.json` is the only entry point.

### Schema

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
  `"node:<layer>:<i>"` merges; `"state:<n>"` compute-state; `"aux-witness"`; a
  `"default"` fallback. A bare integer `N` = `{cores:N, cost:N, priority:0}`.
- **cores** — rayon threads for the job (→ `KIMCHI_PROVE_THREADS`).
  `cores > cost` oversubscribes.
- **cost** — budget the job draws; it dispatches only when the free budget
  covers it. `cost:0` never blocks.
- **priority** — orders *ready* jobs (higher first).
- **worker** — pins the job to a named worker; `run.sh` derives the worker set
  and each worker's base shard from these. Every base circuit `0..23` must be
  assigned, or the run aborts.

### Retuning for other hardware

The wins that reached ~101 s: free the critical-path worker early (more cores on
its base circuit), co-locate the serial `state:8–11` chain on one worker, and
widen the deep merge tail (`node:3/4/5`) once RAM is free. `configs/gen.py`
generates starting configs. Watch `minAvail`; dipping below ~1–2 GB risks OOM.

## Files

- `run.sh` — entry point: `run.sh CONFIG.json`.
- `gantt.py` — ASCII Gantt (per-job + `--by-worker`) from a DAG log.
- `bench.sh` — lower-level harness `run.sh` calls (worker startup, env, timing).
- `configs/het86.json` — the reference config; `configs/gen.py` — generator.
