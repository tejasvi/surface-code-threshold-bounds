#!/usr/bin/env bash
# box_nrun2.sh NAME LIST JOBS: run on a build machine (inside one job) from a lean_count copy whose modules were built
# there by lake (oleans and shared libraries in .lake/build/lib/lean). Compiles the native check modules
# QEC/Checks/NAME/<m>.lean named in LIST, JOBS at once, each its own lean process (threads 1, timeout 3600 s), with
# the core and data shared libraries loaded (--load-dynlib). Outputs .lake/build/lib/lean/QEC/Checks/NAME/<m>.olean;
# log: nrun_NAME.log (module, status, seconds, max RSS KB).
set -uo pipefail
NAME=$1; LIST=$2; JOBS=${3:-40}
export NAME LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1
export LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
L=$PWD/.lake/build/lib/lean
export LEAN_PATH=$L
DL=""
for b in Core Load SeamC SeamLoad; do DL="$DL --load-dynlib=$L/QECCount_QECCountComp_$b.so"; done
for so in "$L"/QECCount_QECCountComp_Data_${NAME}_C*.so; do DL="$DL --load-dynlib=$so"; done
DL="$DL --load-dynlib=$L/QECCount_QECCountComp_Data_${NAME}.so"
export DL L
mkdir -p "$L/QEC/Checks/$NAME" ntimes
one() {
  m=$1
  t0=$(date +%s)
  # shellcheck disable=SC2086
  /usr/bin/time -o "ntimes/${NAME}_$m.txt" -f '%M' timeout -k 15 3600 "$LEAN" $DL \
    -o "$L/QEC/Checks/$NAME/$m.olean.tmp" "QEC/Checks/$NAME/$m.lean" > "ntimes/${NAME}_$m.out" 2>&1
  rc=$?
  t1=$(date +%s)
  if [ $rc -eq 0 ]; then mv "$L/QEC/Checks/$NAME/$m.olean.tmp" "$L/QEC/Checks/$NAME/$m.olean"; st=OK
  else rm -f "$L/QEC/Checks/$NAME/$m.olean.tmp"; st="FAIL($rc)"; fi
  echo "$m $st $((t1 - t0)) $(tail -1 "ntimes/${NAME}_$m.txt" 2>/dev/null)" >> "nrun_$NAME.log"
}
export -f one
xargs -P "$JOBS" -n 1 bash -c 'one "$0"' < "$LIST"
echo "nrun $NAME done: $(grep -c ' OK ' "nrun_$NAME.log") OK, $(grep -vc ' OK ' "nrun_$NAME.log") not OK"
