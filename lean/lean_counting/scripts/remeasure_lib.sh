#!/usr/bin/env bash
# remeasure_lib.sh FILE...: elaborate each proof-library source once more (scripts/chk.sh lean: one core, guards) and
# append "FILE elapsed_s user_s sys_s maxRSS_KB rc" to logs/remeasure_lib.txt (rebuild cost of the proof library,
# Mathlib excluded; the elapsed time includes the guard's polling, so user + sys is the cost).
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
mkdir -p .tmp logs
for f in "$@"; do
  /usr/bin/time -o .tmp/time_lib.txt -f "%e %U %S %M %x" bash scripts/chk.sh lean "$f" > .tmp/relib.out 2>&1
  echo "$f $(tail -n 1 .tmp/time_lib.txt)" >> logs/remeasure_lib.txt
done
