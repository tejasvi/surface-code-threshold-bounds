#!/usr/bin/env bash
# box_rebuild_stale.sh NAME PREFIX CUTOFF JOBS ASMJOBS THM: on the assembly machine (inside one job), in
# $KT_DIR: the check oleans lib/QEC/KChecks/NAME/PREFIX*.olean dated at or before CUTOFF (touch -d
# format; use @EPOCH), i.e. possibly compiled from an earlier generator version before the sources were
# rewritten, are moved (not deleted) to stale_NAME_PREFIX/ and compiled again from the current sources
# (scripts/box_ktrun.sh, JOBS at once; their OK lines are appended to ktrun_NAME.log); every moved olean is then compared
# with its rebuilt one; then the whole assembly is compiled again against them (scripts/box_ktasm.sh NAME ASMJOBS THM;
# the earlier assembly log is kept as ktasm_NAME.before_rebuild.log). Summary: rebuild_NAME_PREFIX.txt.
set -uo pipefail
NAME=$1; PFX=$2; CUT=$3; JOBS=$4; AJ=$5; THM=$6
K=${KT_DIR:?set KT_DIR to the kernel-route work directory}
cd "$K" || exit 2
O=lib/QEC/KChecks/$NAME
S=stale_${NAME}_$PFX
L=rebuild_${NAME}_$PFX.list
R=rebuild_${NAME}_$PFX.txt
touch -d "$CUT" ".cut_$NAME"
find "$O" -maxdepth 1 -name "$PFX[0-9]*.olean" ! -newer ".cut_$NAME" -printf '%f\n' | sed 's/\.olean$//' | LC_ALL=C sort > "$L"
n=$(wc -l < "$L")
echo "$(date -u +%T) $n $PFX oleans of $NAME dated before $CUT" > "$R"
[ "$n" -gt 0 ] || exit 0
mkdir -p "$S"
while read -r m; do mv "$O/$m.olean" "$S/$m.olean"; done < "$L"
echo "$(date -u +%T) moved to $S/" >> "$R"
bash scripts/box_ktrun.sh "$NAME" "$L" "$JOBS"
ok=$(awk 'NR == FNR {s[$1] = 1; next} ($1 in s) {last[$1] = $2} END {n = 0; for (m in s) if (last[m] == "OK") n++; print n}' "$L" "ktrun_$NAME.log")
missing=0; same=0; diff=0
while read -r m; do
  if [ ! -f "$O/$m.olean" ]; then missing=$((missing + 1))
  elif cmp -s "$O/$m.olean" "$S/$m.olean"; then same=$((same + 1))
  else diff=$((diff + 1)); fi
done < "$L"
echo "$(date -u +%T) rebuilt: last ktrun status OK for $ok of $n; olean missing $missing; byte-identical to the old one $same; different $diff" >> "$R"
[ "$missing" -eq 0 ] || { echo "rebuild incomplete: no assembly" >> "$R"; exit 3; }
[ -f "ktasm_$NAME.log" ] && mv "ktasm_$NAME.log" "ktasm_$NAME.before_rebuild.log"
bash scripts/box_ktasm.sh "$NAME" "$AJ" "$THM"
echo "$(date -u +%T) assembly: $(tail -2 "ktasm_$NAME.log" | tr '\n' ' ')" >> "$R"
cat "$R"
