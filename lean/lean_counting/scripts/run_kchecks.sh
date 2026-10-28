#!/usr/bin/env bash
# run_kchecks.sh NAME [MOD ...]: compile the kernel check modules QEC/KChecks/NAME/<MOD>.lean (default: all of
# LIST.txt). They use `decide +kernel` only (no native code is loaded). Each module: its own lean process, one core
# (taskset on an idle core), threads 1, nice 10, timeout 590 s, address space AS_KB (default 64 GB), an optional core-hour
# guard (GUARD; cap CAP core-h per module, default 0.25). JOBS modules at once (default 1). A module whose .olean
# exists is skipped. Log: logs/kchecks_NAME.log (module, status, seconds, max RSS KB).
set -uo pipefail
P=$(cd "$(dirname "$0")/.." && pwd)
cd "$P" || exit 2
NAME=$1; shift
export LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
export GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=1 TMPDIR="$P/.tmp" NAME P
export GUARD=${GUARD:-}  # optional core-hour guard, run as: python3 GUARD LOG CAP --run -- CMD
export CAP=${CAP:-0.25} AS_KB=${AS_KB:-64000000}
export LIB=.lake/build/lib/lean
JOBS=${JOBS:-1}
mkdir -p "$LIB/QEC/KChecks/$NAME" logs
one() {
  nm=$1
  out=$LIB/QEC/KChecks/$NAME/$nm.olean
  [ -f "$out" ] && { echo "$nm SKIP" >> "logs/kchecks_$NAME.log"; return 0; }
  core=$(if [ -n "${PICK_CORE:-}" ]; then bash "$PICK_CORE"; else echo "0-$(( $(nproc) - 1 ))"; fi)
  t0=$(date +%s)
  ( ulimit -v "$AS_KB"; ${GUARD:+python3 -I -B "$GUARD" "$P/logs/guard.log" "$CAP" --run --} \
      /usr/bin/time -o "logs/ktime_${NAME}_$nm.txt" -f '%M' timeout -k 15 590 nice -n 10 taskset -c "$core" \
      lake env lean -o "$out.tmp" "QEC/KChecks/$NAME/$nm.lean" ) > "logs/kout_${NAME}_$nm.txt" 2>&1
  rc=$?
  t1=$(date +%s)
  if [ $rc -eq 0 ]; then mv "$out.tmp" "$out"; st=OK; else rm -f "$out.tmp"; st="FAIL($rc)"; fi
  echo "$nm $st $((t1 - t0)) $(tail -1 "logs/ktime_${NAME}_$nm.txt" 2>/dev/null)" >> "logs/kchecks_$NAME.log"
}
export -f one
if [ $# -gt 0 ]; then printf '%s\n' "$@"; else cat "QEC/KChecks/$NAME/LIST.txt"; fi | xargs -P "$JOBS" -n 1 bash -c 'one "$0"'
