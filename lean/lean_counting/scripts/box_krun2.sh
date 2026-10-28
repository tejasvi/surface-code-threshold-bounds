#!/usr/bin/env bash
# box_krun2.sh NAME LIST JOBS: run on a build machine (inside one job) from a lean_count copy whose QECCountComp modules
# were built there by lake (.lake/build/lib/lean). Compiles the kernel check modules QEC/KChecks/NAME/<m>.lean named in
# LIST, JOBS at once, each its own lean process (threads 1, timeout 7200 s). Outputs
# .lake/build/lib/lean/QEC/KChecks/NAME/<m>.olean; log: krun_NAME.log (module, status, seconds, max RSS KB).
set -uo pipefail
NAME=$1; LIST=$2; JOBS=${3:-40}
export NAME LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1
export LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
L=$PWD/.lake/build/lib/lean
export LEAN_PATH=$L L
mkdir -p "$L/QEC/KChecks/$NAME" ktimes
one() {
  m=$1
  t0=$(date +%s)
  /usr/bin/time -o "ktimes/${NAME}_$m.txt" -f '%M' timeout -k 15 7200 "$LEAN" \
    -o "$L/QEC/KChecks/$NAME/$m.olean.tmp" "QEC/KChecks/$NAME/$m.lean" > "ktimes/${NAME}_$m.out" 2>&1
  rc=$?
  t1=$(date +%s)
  if [ $rc -eq 0 ]; then mv "$L/QEC/KChecks/$NAME/$m.olean.tmp" "$L/QEC/KChecks/$NAME/$m.olean"; st=OK
  else rm -f "$L/QEC/KChecks/$NAME/$m.olean.tmp"; st="FAIL($rc)"; fi
  echo "$m $st $((t1 - t0)) $(tail -1 "ktimes/${NAME}_$m.txt" 2>/dev/null)" >> "krun_$NAME.log"
}
export -f one
xargs -P "$JOBS" -n 1 bash -c 'one "$0"' < "$LIST"
echo "krun $NAME done: $(grep -c ' OK ' "krun_$NAME.log") OK, $(grep -vc ' OK ' "krun_$NAME.log") not OK"
