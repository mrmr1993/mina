# Converting SP1 proofs with nori-proof-converter

## Prerequisites

- Docker installed
- Pull the image:
  ```bash
  docker pull mrmr1993/nori-proof-converter:latest
  ```

## Setup

Create directories for worker sockets, the proving key cache, proof I/O, and
shared working state:

```bash
mkdir -p /tmp/nori-socket /tmp/nori-cache-dir /tmp/nori-proofs /tmp/nori-work
```

Copy your input proof into the proofs directory:

```bash
cp /path/to/your/proof.json /tmp/nori-proofs/
```

## Step 1: Generate proving keys

On the first run, you need to generate and cache the proving keys. This is a
one-time cost per `--cache-dir`.

```bash
docker run --rm \
  -v /tmp/nori-socket:/sockets \
  -v /tmp/nori-cache-dir:/cache \
  -e MINA_USE_MMAP_CACHE=1 \
  mrmr1993/nori-proof-converter:latest \
  start-workers --system plonk --count 1 \
  --socket-dir /sockets/ --cache-dir /cache/ --circuits all
```

Wait for it to finish loading all circuits (you'll see log output for each
one), then kill it with Ctrl-C.

## Step 2: Start proving workers

Start the workers in the background. There are two suggested configurations
depending on your machine.

**Standard (20 cores / 20GB RAM):**

```bash
docker run --rm -d --name nori-workers \
  -v /tmp/nori-socket:/sockets \
  -v /tmp/nori-cache-dir:/cache \
  -v /tmp/nori-work:/tmp \
  -e MINA_USE_MMAP_CACHE=1 \
  -e RAYON_NUM_THREADS=4 \
  mrmr1993/nori-proof-converter:latest \
  start-workers --system plonk --count 7 \
  --socket-dir /sockets/ --cache-dir /cache/ \
  --circuits 19-23,layer1,node --skip-verify
```

**Heavy (48 cores / 128GB+ RAM):**

```bash
docker run --rm -d --name nori-workers \
  -v /tmp/nori-socket:/sockets \
  -v /tmp/nori-cache-dir:/cache \
  -v /tmp/nori-work:/tmp \
  -e MINA_USE_MMAP_CACHE=1 \
  -e RAYON_NUM_THREADS=5 \
  mrmr1993/nori-proof-converter:latest \
  start-workers --system plonk --count 12 \
  --socket-dir /sockets/ --cache-dir /cache/ \
  --circuits all --skip-verify
```

Wait for the workers to finish loading before submitting proofs. You can watch
the logs with:

```bash
docker logs -f nori-workers
```

### Tuning

- `--count` controls the number of parallel worker processes.
- `RAYON_NUM_THREADS` limits the number of cores each worker uses.
- `--circuits` selects which circuits the workers load. Use `all` to load
  everything, or a comma-separated list (e.g. `19-23,layer1,node`) to load a
  subset.

As a rule of thumb, `count * RAYON_NUM_THREADS` should be slightly larger than
the number of cores, to give better CPU saturation by allowing processes to
'steal' each others' cores while the single-threaded portions are running.

## Step 3: Convert a proof

With the workers running, submit a proof for conversion. The pipeline container
must share the same `/tmp` volume as the workers so they can exchange working
state:

```bash
docker run --rm \
  -v /tmp/nori-socket:/sockets \
  -v /tmp/nori-proofs:/proofs \
  -v /tmp/nori-work:/tmp \
  mrmr1993/nori-proof-converter:latest \
  sp1ToPlonkDaemonised /proofs/proof.json --workers /sockets/
```

Replace `proof.json` with the filename you copied into `/tmp/nori-proofs/` in
the setup step. The converted proof will be printed to stdout.

To save the output to a file:

```bash
docker run --rm \
  -v /tmp/nori-socket:/sockets \
  -v /tmp/nori-proofs:/proofs \
  -v /tmp/nori-work:/tmp \
  mrmr1993/nori-proof-converter:latest \
  sp1ToPlonkDaemonised /proofs/proof.json --workers /sockets/ \
  > /tmp/nori-proofs/output.json
```

## Cleanup

Stop the workers when done:

```bash
docker stop nori-workers
```
