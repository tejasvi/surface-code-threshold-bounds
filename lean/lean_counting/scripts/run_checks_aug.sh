#!/usr/bin/env bash
# run_checks_aug.sh NAME [MOD ...]: run_checks.sh for an augmented certificate (gen/mkaug.py): compile the check
# modules QEC/Checks/NAME/<MOD>.lean (default: all of LIST.txt) with the precompiled core, AugC and the data loaded
# (--load-dynlib), so that native_decide runs compiled code. Each module: its own lean process, one core (taskset on
# an idle core), threads 1, nice 10, timeout 590 s, address space AS_KB (default 64 GB), an optional core-hour guard
# (GUARD; cap CAP core-h per module, default 0.25). JOBS modules at once (default 1; more only on a large machine). A module whose
# .olean exists is skipped. Log: logs/checks_NAME.log (module, status, seconds, max RSS KB).
# Needs the dynlibs: chk.sh build QECCountComp.AugC:dynlib, QECCountComp.Data.NAME.C<j>:dynlib, QECCountComp.Data.NAME:dynlib.
set -uo pipefail
P=$(cd "$(dirname "$0")/.." && pwd)
cd "$P" || exit 2
NAME=$1; shift
export LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
export GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=1 TMPDIR="$P/.tmp" NAME P
export GUARD=${GUARD:-}  # optional core-hour guard, run as: python3 GUARD LOG CAP --run -- CMD
export CAP=${CAP:-0.25} AS_KB=${AS_KB:-64000000}
JOBS=${JOBS:-1}
export LIB=.lake/build/lib/lean
DL="--load-dynlib=$LIB/QECCount_QECCountComp_Core.so --load-dynlib=$LIB/QECCount_QECCountComp_Load.so"
DL="$DL --load-dynlib=$LIB/QECCount_QECCountComp_SeamLoad.so --load-dynlib=$LIB/QECCount_QECCountComp_AugC.so"
for so in $LIB/QECCount_QECCountComp_Data_${NAME}_C*.so; do DL="$DL --load-dynlib=$so"; done
DL="$DL --load-dynlib=$LIB/QECCount_QECCountComp_Data_${NAME}.so"
export DL
mkdir -p "$LIB/QEC/Checks/$NAME" logs
one() {
  nm=$1
  out=$LIB/QEC/Checks/$NAME/$nm.olean
  [ -f "$out" ] && { echo "$nm SKIP" >> "logs/checks_$NAME.log"; return 0; }
  core=$(if [ -n "${PICK_CORE:-}" ]; then bash "$PICK_CORE"; else echo "0-$(( $(nproc) - 1 ))"; fi)
  t0=$(date +%s)
  ( ulimit -v "$AS_KB"; ${GUARD:+python3 -I -B "$GUARD" "$P/logs/guard.log" "$CAP" --run --} \
      /usr/bin/time -o "logs/time_${NAME}_$nm.txt" -f '%M' timeout -k 15 590 nice -n 10 taskset -c "$core" \
      lake env lean $DL -o "$out.tmp" "QEC/Checks/$NAME/$nm.lean" ) > "logs/out_${NAME}_$nm.txt" 2>&1
  rc=$?
  t1=$(date +%s)
  # the only file this script removes: the failed module's own partial output, a regular file named *.olean.tmp
  if [ $rc -eq 0 ]; then mv "$out.tmp" "$out"; st=OK
  else case "$out.tmp" in *.olean.tmp) [ -f "$out.tmp" ] && rm -f -- "$out.tmp" ;; esac; st="FAIL($rc)"; fi
  echo "$nm $st $((t1 - t0)) $(tail -1 "logs/time_${NAME}_$nm.txt" 2>/dev/null)" >> "logs/checks_$NAME.log"
}
export -f one
if [ $# -gt 0 ]; then printf '%s\n' "$@"; else cat "QEC/Checks/$NAME/LIST.txt"; fi | xargs -P "$JOBS" -n 1 bash -c 'one "$0"'
