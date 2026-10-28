#!/usr/bin/env bash
# box_fleet_job.sh NAME:LIST:JOBS ...: run on a build machine (inside one job) in $LC_DIR
# (prepared beforehand): the phases one after the other, each `box_krun2.sh NAME LIST JOBS`
# (kernel check modules, JOBS at once). The phase sizes are chosen so that the sum of the peak memories times 1.5
# stays under the unit's memory cap.
set -uo pipefail
cd "$LC_DIR" || exit 2
for ph in "$@"; do
  IFS=: read -r name list jobs <<< "$ph"
  echo "[fleet] $(date -u -Is) phase $name $list jobs=$jobs modules=$(wc -l < "$list")"
  bash scripts/box_krun2.sh "$name" "$list" "$jobs"
done
echo "[fleet] $(date -u -Is) all phases done"
