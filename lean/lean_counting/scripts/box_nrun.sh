#!/usr/bin/env bash
# box_nrun.sh NAME LIST JOBS: run on a build machine (inside one job), in a work directory holding the check sources, the oleans in lib/ and the shared libraries in so/.
# Compiles the native check modules QEC/Checks/NAME/<m>.lean named in LIST, JOBS at once, each its own lean process
# (threads 1, timeout 3600 s), with LEAN_PATH=lib (oleans copied from the workstation) and every shared library in so/
# loaded (--load-dynlib), so that native_decide runs the compiled checks. Outputs out/QEC/Checks/NAME/<m>.olean;
# log: nrun_NAME.log (module, status, seconds, max RSS KB).
set -uo pipefail
NAME=$1; LIST=$2; JOBS=${3:-40}
export NAME LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1
export LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
export LEAN_PATH=$PWD/lib
# core libraries first, then the data chunks, then the data module
DL=""
for b in Core Load SeamLoad AugC; do DL="$DL --load-dynlib=$PWD/so/QECCount_QECCountComp_$b.so"; done
for so in "$PWD"/so/QECCount_QECCountComp_Data_${NAME}_C*.so; do DL="$DL --load-dynlib=$so"; done
DL="$DL --load-dynlib=$PWD/so/QECCount_QECCountComp_Data_${NAME}.so"
export DL
mkdir -p "out/QEC/Checks/$NAME" ntimes
one() {
  m=$1
  t0=$(date +%s)
  # shellcheck disable=SC2086
  /usr/bin/time -o "ntimes/${NAME}_$m.txt" -f '%M' timeout -k 15 3600 "$LEAN" $DL \
    -o "out/QEC/Checks/$NAME/$m.olean.tmp" "QEC/Checks/$NAME/$m.lean" > "ntimes/${NAME}_$m.out" 2>&1
  rc=$?
  t1=$(date +%s)
  if [ $rc -eq 0 ]; then mv "out/QEC/Checks/$NAME/$m.olean.tmp" "out/QEC/Checks/$NAME/$m.olean"; st=OK
  else rm -f "out/QEC/Checks/$NAME/$m.olean.tmp"; st="FAIL($rc)"; fi
  echo "$m $st $((t1 - t0)) $(tail -1 "ntimes/${NAME}_$m.txt" 2>/dev/null)" >> "nrun_$NAME.log"
}
export -f one
xargs -P "$JOBS" -n 1 bash -c 'one "$0"' < "$LIST"
echo "nrun $NAME done: $(grep -c ' OK ' "nrun_$NAME.log") OK, $(grep -vc ' OK ' "nrun_$NAME.log") not OK"
