#!/usr/bin/env bash
# box_ktrun.sh NAME LIST JOBS: on a build machine (inside one job), in $KT_DIR: compile the kernel
# check modules QEC/KChecks/NAME/<m>.lean named in LIST, JOBS at once, each its own lean process (threads 1, timeout
# 7200 s), oleans into kt/lib; a module whose olean exists is skipped. Log: ktrun_NAME.log (module, status, seconds,
# max RSS KB).
set -uo pipefail
NAME=$1; LIST=$2; JOBS=${3:-40}
K=${KT_DIR:?set KT_DIR to the kernel-route work directory}; LC=${LC_DIR:?set LC_DIR to a lake-built copy of this tree}
export LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
LP=$K/lib
for p in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do
  LP=$LP:$LC/.lake/packages/$p/.lake/build/lib/lean
done
export LEAN_PATH=$LP LEAN_NUM_THREADS=1 NAME K
cd "$K" || exit 2
O=$K/lib/QEC/KChecks/$NAME
export O
mkdir -p "$O" ktimes
one() {
  m=$1
  [ -f "$O/$m.olean" ] && return 0
  t0=$(date +%s)
  /usr/bin/time -o "ktimes/${NAME}_$m.txt" -f '%M' timeout -k 15 7200 "$LEAN" -o "$O/$m.olean.tmp" \
    "QEC/KChecks/$NAME/$m.lean" > "ktimes/${NAME}_$m.out" 2>&1
  rc=$?
  t1=$(date +%s)
  if [ $rc -eq 0 ]; then mv "$O/$m.olean.tmp" "$O/$m.olean"; st=OK
  else rm -f "$O/$m.olean.tmp"; st="FAIL($rc)"; fi
  echo "$m $st $((t1 - t0)) $(tail -1 "ktimes/${NAME}_$m.txt" 2>/dev/null)" >> "ktrun_$NAME.log"
}
export -f one
xargs -P "$JOBS" -n 1 bash -c 'one "$0"' < "$LIST"
echo "ktrun $NAME done: $(command grep -c ' OK ' "ktrun_$NAME.log") OK, $(command grep -vc ' OK ' "ktrun_$NAME.log") not OK"
