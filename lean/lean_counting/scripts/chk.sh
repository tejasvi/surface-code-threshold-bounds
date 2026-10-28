#!/usr/bin/env bash
# chk.sh: run one Lean command in the lean_count project under fixed limits: one core (taskset on an idle
# core, all thread counts 1), timeout 590 s, nice 10, 100 GB address space, git restricted to the file protocol,
# TMPDIR inside the project, and an optional core-hour guard (GUARD; cap CAP core-h, default 0.2).
# Usage:  bash scripts/chk.sh lean FILE.lean        (= lake env lean FILE.lean)
#         bash scripts/chk.sh build [TARGET]        (= lake build [TARGET]; LEAN_NUM_THREADS=1 gives one job)
set -u
P=$(cd "$(dirname "$0")/.." && pwd)
cd "$P" || exit 2
export LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
export GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=1 GIT_TERMINAL_PROMPT=0
export TMPDIR="$P/.tmp"
GUARD=${GUARD:-}  # optional core-hour guard, run as: python3 GUARD LOG CAP --run -- CMD
CAP=${CAP:-0.2}
CORE=$(if [ -n "${PICK_CORE:-}" ]; then bash "$PICK_CORE"; else echo "0-$(( $(nproc) - 1 ))"; fi)
ulimit -v "${AS_KB:-100000000}"   # AS_KB=300000000 for modules importing the R10 data (thread creation fails at 100 GB)
mode=$1; shift
case "$mode" in
  lean)  exec env PYTHONDONTWRITEBYTECODE=1 ${GUARD:+python3 -I -B "$GUARD" "$P/logs/guard.log" "$CAP" --run --} \
           timeout -k 15 590 nice -n 10 taskset -c "$CORE" lake env lean "$@" ;;
  build) exec env PYTHONDONTWRITEBYTECODE=1 ${GUARD:+python3 -I -B "$GUARD" "$P/logs/guard.log" "$CAP" --run --} \
           timeout -k 15 590 nice -n 10 taskset -c "$CORE" lake build "$@" ;;
  *) echo "usage: chk.sh lean FILE | build [TARGET]" >&2; exit 2 ;;
esac
