#!/usr/bin/env bash
# box_kassemble.sh NAME [THM]: run on a build machine (inside one job). Writes the assembly modules of the version-2
# kernel certificate NAME (gen/mkkall2.py, in $LC_DIR) and compiles them: A<j> in order, the P<j>
# in parallel, then All; then the theorem file QEC/Thm/THM.lean with #print axioms of its theorems. The proof modules
# (QEC.Count.*, Mathlib) come from $LC2_DIR (built there by lake), the kernel data and check
# oleans from lc. Log: kasm_NAME.log.
set -uo pipefail
NAME=$1; THM=${2:-}
# (run on one large machine)
LC=${LC_DIR:?set LC_DIR to a lake-built copy of this tree}; LC2=${LC2_DIR:?set LC2_DIR to a lake-built copy of this tree holding the proof modules}
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
# one root for every QEC.* olean: the proof modules built in lc2 are copied next to the check oleans in lc
# (tar --skip-old-files); Lean resolves a module under the first root that has its top-level directory
LP=$LC/.lake/build/lib/lean
for p in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do
  LP=$LP:$LC/.lake/packages/$p/.lake/build/lib/lean
done
export LEAN_PATH=$LP LEAN_NUM_THREADS=1
cd "$LC" || exit 2
LOG=$LC/kasm_$NAME.log
python3 -I -B gen/mkkall2.py "$NAME" >> "$LOG" 2>&1 || { echo "mkkall2 failed" >> "$LOG"; exit 3; }
O=$LC/.lake/build/lib/lean/QEC/KChecks/$NAME
comp() {
  t0=$(date +%s)
  "$LEAN" -o "$O/$1.olean" "QEC/KChecks/$NAME/$1.lean" > "$LC/kasm_${NAME}_$1.out" 2>&1
  rc=$?
  echo "$1 rc=$rc $(( $(date +%s) - t0 )) s" >> "$LOG"
  return $rc
}
export -f comp
export NAME LC O LEAN LOG
j=0
while [ -f "QEC/KChecks/$NAME/A$j.lean" ]; do comp "A$j" || exit 4; j=$((j + 1)); done
ls QEC/KChecks/$NAME/P*.lean 2>/dev/null | sed 's,.*/,,; s,\.lean$,,' | xargs -r -P 16 -n 1 bash -c 'comp "$0"'
comp All || exit 5
if [ -n "$THM" ]; then
  mkdir -p "$LC/.tmp"
  cp "$LC2/QEC/Thm/$THM.lean" "$LC/.tmp/${THM}_ax.lean"
  awk '$1 == "theorem" {print "#print axioms QEC." $2}' "$LC2/QEC/Thm/$THM.lean" >> "$LC/.tmp/${THM}_ax.lean"
  "$LEAN" "$LC/.tmp/${THM}_ax.lean" > "$LC/kasm_${NAME}_thm.out" 2>&1
  echo "theorem rc=$?" >> "$LOG"
fi
echo "done $(date -u -Is)" >> "$LOG"
