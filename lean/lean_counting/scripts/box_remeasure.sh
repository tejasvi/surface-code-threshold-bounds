#!/usr/bin/env bash
# box_remeasure.sh: on a build machine (inside one job), elaborate the final assembly modules and theorem files of the
# version-2 kernel certificates once more (no output files) and record elapsed time and max RSS (/usr/bin/time) in
# $RESULTS (default ./remeasure.txt), for the build table.
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
for f in QEC/KChecks/A10K2/All.lean QEC/Thm/PlanarK10.lean QEC/KChecks/D2M8K2/All.lean QEC/Thm/PhenomK8.lean; do
  /usr/bin/time -o "$R" -a -f "$f %e s %M KB rc=%x" "$LEAN" "$f" > /dev/null 2>&1
done
echo "remeasure done" >> "$R"
