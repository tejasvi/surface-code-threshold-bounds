#!/usr/bin/env bash
# remeasure_thm.sh THM...: elaborate QEC/Thm/<THM>.lean once more with #print axioms of its theorems appended
# (copy in .tmp/<THM>_ax.lean), one core; append "THM seconds maxRSS_KB rc native_axioms" to logs/remeasure_thm.txt
# and keep the output in logs/remeasure_<THM>.out.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
export LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
mkdir -p .tmp logs
for t in "$@"; do
  f=QEC/Thm/$t.lean
  [ -f "$f" ] || { echo "$t missing" >> logs/remeasure_thm.txt; continue; }
  cp "$f" ".tmp/${t}_ax.lean"
  awk '$1 == "theorem" {print "#print axioms QEC." $2}' "$f" >> ".tmp/${t}_ax.lean"
  /usr/bin/time -o .tmp/time_$t.txt -f "%e %M %x" timeout 580 lake env lean ".tmp/${t}_ax.lean" > "logs/remeasure_$t.out" 2>&1
  na=$(command grep -o '[A-Za-z0-9_.]*\._native\.native_decide\.ax[A-Za-z0-9_]*' "logs/remeasure_$t.out" | sort -u | wc -l)
  echo "$t $(tail -n 1 .tmp/time_$t.txt) native_axioms=$na" >> logs/remeasure_thm.txt
done
