#!/usr/bin/env bash
# box_kdata_recheck.sh NAME JOBS: on a build machine (inside one job), in $KT_DIR: compile the
# kernel data modules of NAME again from their current sources (QECCountComp/KData/NAME*.lean) into the scratch tree
# kt/.vr_NAME/lib (subtree files JOBS at once, then U, then NAME; imports resolved in the scratch tree first), and compare
# every olean byte for byte with the one in kt/lib that the check and assembly modules were compiled against.
# Writes vr_NAME.txt: the two sha256 lists' digests and the number of differing or missing oleans (0 = the oleans in
# use are exactly what the current sources compile to).
set -uo pipefail
NAME=$1; JOBS=${2:-40}
K=${KT_DIR:?set KT_DIR to the kernel-route work directory}; LC=${LC_DIR:?set LC_DIR to a lake-built copy of this tree}
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
S=$K/.vr_$NAME
cd "$K" || exit 2
mkdir -p "$S/lib/QECCountComp/KData/$NAME"
# Lean takes a package's modules from the first search-path entry holding the package directory, so the scratch tree
# gets copies of the core oleans (lib/QECCountComp/*.olean, regular files) next to the rebuilt kernel data
for f in "$K"/lib/QECCountComp/*.olean; do cp "$f" "$S/lib/QECCountComp/"; done
LP=$S/lib:$K/lib
for p in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do
  LP=$LP:$LC/.lake/packages/$p/.lake/build/lib/lean
done
export LEAN LEAN_PATH=$LP LEAN_NUM_THREADS=1 NAME S
one() { "$LEAN" -o "$S/lib/QECCountComp/KData/$NAME/$1.olean" "QECCountComp/KData/$NAME/$1.lean" > /dev/null 2>&1 || echo "$1 failed"; }
export -f one
ls "QECCountComp/KData/$NAME" | sed -n 's/\.lean$//p' | command grep -v '^U$' | xargs -P "$JOBS" -n 1 bash -c 'one "$0"' > "vr_$NAME.fail"
one U >> "vr_$NAME.fail"
"$LEAN" -o "$S/lib/QECCountComp/KData/$NAME.olean" "QECCountComp/KData/$NAME.lean" > /dev/null 2>&1 || echo "root failed" >> "vr_$NAME.fail"
( cd "$S" && { echo "lib/QECCountComp/KData/$NAME.olean"; find "lib/QECCountComp/KData/$NAME" -name '*.olean'; } | LC_ALL=C sort |
  xargs sha256sum ) > "vr_$NAME.sha256"
{ echo "lib/QECCountComp/KData/$NAME.olean"; find "lib/QECCountComp/KData/$NAME" -name '*.olean'; } | LC_ALL=C sort |
  xargs sha256sum > "vr_${NAME}_inuse.sha256"
d=$(diff "vr_$NAME.sha256" "vr_${NAME}_inuse.sha256" | command grep -c '^[<>]')
{ echo "rebuilt $(wc -l < "vr_$NAME.sha256") oleans (list $(sha256sum < "vr_$NAME.sha256" | cut -c1-16)), in use $(wc -l < "vr_${NAME}_inuse.sha256") (list $(sha256sum < "vr_${NAME}_inuse.sha256" | cut -c1-16)); lines in only one list: $d (0 = identical); compile failures: $(wc -l < "vr_$NAME.fail")"; } > "vr_$NAME.txt"
cat "vr_$NAME.txt"
