#!/usr/bin/env bash
# box_krun.sh LIST JOBS: run on a build machine (inside one job), in a work directory holding the check sources, the core oleans in lib/ and this script.
# LIST has lines "NAME MODULE"; compiles QEC/KChecks/NAME/MODULE.lean, JOBS at once, each its own lean process
# (threads 1, timeout 1800 s), with LEAN_PATH=lib (the QECCountComp oleans copied from the workstation). Outputs
# out/QEC/KChecks/NAME/MODULE.olean; log: krun.log (name, module, status, seconds, max RSS KB).
set -uo pipefail
LIST=$1; JOBS=${2:-96}
export LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1
export LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
export LEAN_PATH=$PWD/lib
mkdir -p times
one() {
  n=$1; m=$2
  mkdir -p "out/QEC/KChecks/$n"
  t0=$(date +%s)
  /usr/bin/time -o "times/${n}_$m.txt" -f '%M' timeout -k 15 1800 "$LEAN" -o "out/QEC/KChecks/$n/$m.olean.tmp" \
    "QEC/KChecks/$n/$m.lean" > "times/${n}_$m.out" 2>&1
  rc=$?
  t1=$(date +%s)
  if [ $rc -eq 0 ]; then mv "out/QEC/KChecks/$n/$m.olean.tmp" "out/QEC/KChecks/$n/$m.olean"; st=OK
  else rm -f "out/QEC/KChecks/$n/$m.olean.tmp"; st="FAIL($rc)"; fi
  echo "$n $m $st $((t1 - t0)) $(tail -1 "times/${n}_$m.txt" 2>/dev/null)" >> krun.log
}
export -f one
xargs -P "$JOBS" -n 2 bash -c 'one "$0" "$1"' < "$LIST"
echo "krun done: $(grep -c ' OK ' krun.log) OK, $(grep -vc ' OK ' krun.log) not OK"
