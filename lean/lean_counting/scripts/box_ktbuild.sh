#!/usr/bin/env bash
# box_ktbuild.sh NAME JOBS: on a build machine (inside one job), in $KT_DIR: compile the kernel data
# modules of NAME into kt/lib (the subtree files in parallel, JOBS at once; then U; then NAME). Log: ktbuild_NAME.log.
set -uo pipefail
NAME=$1; JOBS=${2:-40}
K=${KT_DIR:?set KT_DIR to the kernel-route work directory}; LC=${LC_DIR:?set LC_DIR to a lake-built copy of this tree}
export LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
LP=$K/lib
for p in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do
  LP=$LP:$LC/.lake/packages/$p/.lake/build/lib/lean
done
export LEAN_PATH=$LP LEAN_NUM_THREADS=1 NAME K
cd "$K" || exit 2
mkdir -p "lib/QECCountComp/KData/$NAME"
LOG=$K/ktbuild_$NAME.log
export LOG
one() {
  f=$1; t0=$(date +%s)
  /usr/bin/time -o "$K/.t_${NAME}_$f.txt" -f '%M' "$LEAN" -o "lib/QECCountComp/KData/$NAME/$f.olean" \
    "QECCountComp/KData/$NAME/$f.lean" > "$K/.o_${NAME}_$f.txt" 2>&1
  rc=$?
  echo "$f rc=$rc $(( $(date +%s) - t0 )) $(tail -1 "$K/.t_${NAME}_$f.txt" 2>/dev/null)" >> "$LOG"
  return $rc
}
export -f one
ls "QECCountComp/KData/$NAME" | sed -n 's/\.lean$//p' | command grep -v '^U$' | xargs -P "$JOBS" -n 1 bash -c 'one "$0"'
one U || { echo "U failed" >> "$LOG"; exit 3; }
"$LEAN" -o "lib/QECCountComp/KData/$NAME.olean" "QECCountComp/KData/$NAME.lean" >> "$LOG" 2>&1 || { echo "root failed" >> "$LOG"; exit 4; }
echo "ktbuild $NAME done $(date -u +%T)" >> "$LOG"
