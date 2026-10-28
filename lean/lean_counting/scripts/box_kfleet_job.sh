#!/usr/bin/env bash
# box_kfleet_job.sh SRC OUT KIND PACK DEPTH SUBS IROW IDX NBOX JR JE: on a build machine (inside one job), in
# $KT_DIR (prepared beforehand with the generators, scripts, core and proof oleans, data sources and hints): generate the kernel certificate OUT from the
# compiled-evaluation data SRC and its hints (gen/mk<KIND>.py, KIND = kseam or kaug, PACK = 1 for packed trees; the
# same files on every box), build its kernel data, then compile this box's share of the check modules (every NBOX-th
# line of LIST.txt from line IDX, IDX a comma list): the row and internal-row modules JR at once and the start-prefix
# modules JE at once, as PHASES below says (JR, JE sized so that the unit's peak memory times 1.5 stays under its cap).
set -uo pipefail
SRC=$1; OUT=$2; KIND=$3; PACK=$4; DEPTH=$5; SUBS=$6; IROW=$7; IDX=$8; NBOX=$9; JR=${10}; JE=${11}
K=${KT_DIR:?set KT_DIR to the kernel-route work directory}
cd "$K" || exit 2
echo "[kfleet] $(date -u -Is) start $*"
if [ ! -f "QECCountComp/KData/$OUT.lean" ]; then
  PACK=$PACK python3 -I -B "gen/mk$KIND.py" "$SRC" "$OUT" masks "$DEPTH" "$SUBS" "$IROW" > "gen_$OUT.json" || exit 3
  echo "[kfleet] $(date -u -Is) generated: $(cut -c1-300 "gen_$OUT.json")"
fi
if [ ! -f "lib/QECCountComp/KData/$OUT.olean" ]; then
  bash scripts/box_ktbuild.sh "$OUT" 300 || exit 4
  echo "[kfleet] $(date -u -Is) kernel data built"
fi
awk -v ids="$IDX" -v n="$NBOX" 'BEGIN { k = split(ids, a, ","); for (j = 1; j <= k; j++) s[a[j]] = 1 }
  ((NR - 1) % n) in s' "QEC/KChecks/$OUT/LIST.txt" > "share_$OUT.txt"
command grep -v '^E' "share_$OUT.txt" > "share_${OUT}_R.txt"
command grep '^E' "share_$OUT.txt" > "share_${OUT}_E.txt"
echo "[kfleet] $(date -u -Is) share: $(wc -l < "share_${OUT}_R.txt") row modules, $(wc -l < "share_${OUT}_E.txt") start modules"
# PHASES (environment): R = rows only, E = start modules only, RE = both (default): one queue, the start modules first
# (their running times have a long tail) and the rows filling in, max(JR, JE) at once. (Until 26 Oct 19:55Z RE ran the
# rows, then the start modules.)
case "${PHASES:-RE}" in
  R) bash scripts/box_ktrun.sh "$OUT" "share_${OUT}_R.txt" "$JR"
     echo "[kfleet] $(date -u -Is) row phase done" ;;
  E) bash scripts/box_ktrun.sh "$OUT" "share_${OUT}_E.txt" "$JE"
     echo "[kfleet] $(date -u -Is) start phase done" ;;
  *) cat "share_${OUT}_E.txt" "share_${OUT}_R.txt" > "share_${OUT}_ER.txt"
     bash scripts/box_ktrun.sh "$OUT" "share_${OUT}_ER.txt" "$(( JR > JE ? JR : JE ))"
     echo "[kfleet] $(date -u -Is) start and row modules done" ;;
esac
echo "[kfleet] $(date -u -Is) all done: $(command grep -c ' OK ' "ktrun_$OUT.log") OK, $(command grep -vc ' OK ' "ktrun_$OUT.log") not OK"
