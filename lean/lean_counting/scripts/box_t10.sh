#!/usr/bin/env bash
# box_t10.sh PREFIX JOBS: run on a build machine (inside one job) in $LC_DIR (a lean_count copy with
# a private copy of the prebuilt packages). Generates the T10 seam data and check modules from the certificate generator tm2d_seam
# outputs PREFIX.{json,near_keys,seam_H,bulk_states} (gen/mkseam2.py, 20 sort workers), builds the data and core
# shared libraries with lake (parallel), and runs every check module (scripts/box_nrun2.sh, JOBS at once).
set -euo pipefail
PREFIX=$1; JOBS=${2:-90}
# (run on one large machine)
cd "$LC_DIR"
export GIT_ALLOW_PROTOCOL=file GIT_NO_LAZY_FETCH=1 GIT_TERMINAL_PROMPT=0
T=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin
echo "[box_t10] $(date -u -Is) generate"
NPROC=20 python3 -I -B gen/mkseam2.py T10 "$PREFIX" 10 320 8 1 400000 2 "$LC_DIR/.tmp/t10sort" \
  > logs_mkseam2_T10.json
echo "[box_t10] $(date -u -Is) build"
n=$(ls QECCountComp/Data/T10/C*.lean | wc -l)
TG="QECCountComp.Core:dynlib QECCountComp.Load:dynlib QECCountComp.SeamC:dynlib QECCountComp.SeamLoad:dynlib"
for ((j = 0; j < n; j++)); do TG="$TG QECCountComp.Data.T10.C$j:dynlib"; done
TG="$TG QECCountComp.Data.T10:dynlib"
# shellcheck disable=SC2086
LEAN_NUM_THREADS=$JOBS "$T/lake" build $TG > logs_build_T10.txt 2>&1
tail -2 logs_build_T10.txt
echo "[box_t10] $(date -u -Is) checks"
bash scripts/box_nrun2.sh T10 QEC/Checks/T10/LIST.txt "$JOBS"
echo "[box_t10] $(date -u -Is) done"
