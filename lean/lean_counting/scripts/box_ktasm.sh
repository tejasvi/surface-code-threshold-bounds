#!/usr/bin/env bash
# box_ktasm.sh NAME JOBS [THM]: on a build machine (inside one job), in $KT_DIR: compile the assembly
# modules of the kernel certificate NAME (gen/mkkallTA.py): A<j> in order, the P<i> in parallel (JOBS), then All; then,
# if THM is given, the theorem file QEC/Thm/THM.lean with #print axioms of its theorems appended (copy in .tmp/).
# Mathlib and the other packages: $KT_DIR/packages if present, else the $LC_DIR copy. Log: ktasm_NAME.log. Before the P
# modules every check module of LIST.txt must have its olean; WAIT_S (environment, default 0) is how long to wait for
# oleans still being collected from other boxes.
set -uo pipefail
NAME=$1; JOBS=${2:-8}; THM=${3:-}
K=${KT_DIR:?set KT_DIR to the kernel-route work directory}; LC=${LC_DIR:?set LC_DIR to a lake-built copy of this tree}
export LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
PK=$LC/.lake/packages
[ -d "$K/packages" ] && PK=$K/packages
LP=$K/lib
for p in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do
  LP=$LP:$PK/$p/.lake/build/lib/lean
done
export LEAN_PATH=$LP LEAN_NUM_THREADS=1 NAME K
cd "$K" || exit 2
O=$K/lib/QEC/KChecks/$NAME
export O
LOG=$K/ktasm_$NAME.log
export LOG
comp() {
  t0=$(date +%s)
  /usr/bin/time -o "$K/.ta_${NAME}_$1.txt" -f '%M' "$LEAN" -o "$O/$1.olean" "QEC/KChecks/$NAME/$1.lean" > "$K/.ao_${NAME}_$1.txt" 2>&1
  rc=$?
  echo "$1 rc=$rc $(( $(date +%s) - t0 )) s $(tail -1 "$K/.ta_${NAME}_$1.txt" 2>/dev/null) KB" >> "$LOG"
  return $rc
}
export -f comp
if [ -f "QEC/KChecks/$NAME/ALEVELS.txt" ]; then
  # level by level, the A files of one level in parallel
  while read -r line; do
    echo "$line" | tr ' ' '\n' | command grep -v '^$' | xargs -P "$JOBS" -n 1 bash -c 'comp "$0"'
    command grep -q 'rc=[1-9]' "$LOG" && { echo "an assembly module failed" >> "$LOG"; exit 3; }
  done < "QEC/KChecks/$NAME/ALEVELS.txt"
else
  for a in $(ls "QEC/KChecks/$NAME" | sed -n 's/^\(A[0-9]*\)\.lean$/\1/p' | sort -t A -k2 -n); do
    comp "$a" || { echo "assembly $a failed" >> "$LOG"; exit 3; }
  done
fi
# every check module of LIST.txt must have its olean before the P modules (they may still be arriving from other boxes:
# wait up to WAIT_S seconds, default 0)
t0w=$(date +%s)
while m=$(comm -23 <(LC_ALL=C sort "QEC/KChecks/$NAME/LIST.txt") <(ls "$O" | sed -n 's/\.olean$//p' | LC_ALL=C sort) | wc -l)
  [ "$m" -gt 0 ]; do
  [ $(( $(date +%s) - t0w )) -ge "${WAIT_S:-0}" ] && { echo "$m check oleans missing" >> "$LOG"; exit 6; }
  sleep 30
done
echo "all check oleans present $(date -u +%T)" >> "$LOG"
ls "QEC/KChecks/$NAME" | sed -n 's/^\(P[0-9]*_[0-9]*\)\.lean$/\1/p' | xargs -P "$JOBS" -n 1 bash -c 'comp "$0"'
command grep -q 'rc=[1-9]' "$LOG" && { echo "a P module failed" >> "$LOG"; exit 4; }
ls "QEC/KChecks/$NAME" | sed -n 's/^\(P[0-9]*\)\.lean$/\1/p' | xargs -P "$JOBS" -n 1 bash -c 'comp "$0"'
command grep -q 'rc=[1-9]' "$LOG" && { echo "a P module failed" >> "$LOG"; exit 4; }
comp All || { echo "All failed" >> "$LOG"; exit 5; }
echo "ktasm $NAME done $(date -u +%T)" >> "$LOG"
if [ -n "$THM" ]; then
  mkdir -p .tmp
  cp "QEC/Thm/$THM.lean" ".tmp/${THM}_ax.lean"
  awk '$1 == "theorem" {print "#print axioms QEC." $2}' "QEC/Thm/$THM.lean" >> ".tmp/${THM}_ax.lean"
  /usr/bin/time -o "$K/.ta_${NAME}_thm.txt" -f '%e s %M KB' "$LEAN" ".tmp/${THM}_ax.lean" > "$K/thm_${THM}.out" 2>&1
  echo "theorem $THM rc=$? $(tail -1 "$K/.ta_${NAME}_thm.txt")" >> "$LOG"
fi
