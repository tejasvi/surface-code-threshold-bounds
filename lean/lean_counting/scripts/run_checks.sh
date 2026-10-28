#!/usr/bin/env bash
# run_checks.sh NAME [MOD ...]: compile the check modules QEC/Checks/NAME/<MOD>.lean (default: all of LIST.txt)
# with the precompiled core and data loaded (--load-dynlib), so that native_decide runs compiled code. Each module:
# its own lean process, one core (taskset on an idle core), threads 1, nice 10, timeout 590 s, address space
# AS_KB (default 64 GB), an optional core-hour guard (GUARD; cap CAP core-h per module, default 0.25). JOBS modules at once
# (default 1; more only on a large machine). A module whose .olean exists is skipped. Log: logs/checks_NAME.log
# (module, status, seconds, max RSS KB).
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
DL="$DL --load-dynlib=$LIB/QECCount_QECCountComp_Safe.so"
if [ "${SEAM:-0}" = 1 ]; then
  DL="$DL --load-dynlib=$LIB/QECCount_QECCountComp_SeamC.so --load-dynlib=$LIB/QECCount_QECCountComp_SeamLoad.so"
fi
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
  if [ $rc -eq 0 ]; then mv "$out.tmp" "$out"; st=OK; else rm -f "$out.tmp"; st="FAIL($rc)"; fi
  echo "$nm $st $((t1 - t0)) $(tail -1 "logs/time_${NAME}_$nm.txt" 2>/dev/null)" >> "logs/checks_$NAME.log"
}
export -f one
if [ $# -gt 0 ]; then printf '%s\n' "$@"; else cat "QEC/Checks/$NAME/LIST.txt"; fi | xargs -P "$JOBS" -n 1 bash -c 'one "$0"'
