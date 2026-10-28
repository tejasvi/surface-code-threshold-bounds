#!/usr/bin/env bash
# box_remeasure2.sh: on a build machine (inside one job), elaborate the theorem files of the version-2 kernel certificates
# once more (copies with #print axioms appended, .tmp/<THM>_ax.lean) and record elapsed time
# and max RSS in $RESULTS (default ./remeasure.txt); the axioms output goes to remeasure_<THM>.out.
set -uo pipefail
# (run on one large machine)
LC=${LC_DIR:?set LC_DIR to a lake-built copy of this tree}
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
LP=$LC/.lake/build/lib/lean
for p in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do
  LP=$LP:$LC/.lake/packages/$p/.lake/build/lib/lean
done
export LEAN_PATH=$LP LEAN_NUM_THREADS=1
cd "$LC" || exit 2
R=${RESULTS:-$PWD/remeasure.txt}
for t in PlanarK10 PhenomK8; do
  /usr/bin/time -o "$R" -a -f "$t %e s %M KB rc=%x" "$LEAN" ".tmp/${t}_ax.lean" > "$(dirname "$R")/remeasure_$t.out" 2>&1
done
echo "remeasure2 done" >> "$R"
