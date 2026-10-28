#!/usr/bin/env bash
# box_mask.sh NAME NPART: on a build machine (inside one job), in $KM_DIR (prepared by the workstation:
# lib = the oleans of the compiled-evaluation data of NAME and of the core with KernT/KernA, so = their shared
# libraries, MaskNAME.lean): the exclusion hints of NAME by compiled evaluation, the near entries in NPART parts in
# parallel and the bulk entries, then concatenated into masks/NAME_near.txt and masks/NAME_bulk.txt. Log: mask_NAME.log.
set -uo pipefail
NAME=$1; NPART=$2
M=${KM_DIR:?set KM_DIR to the hint workspace}
export LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
export LEAN_PATH=$M/lib LEAN_NUM_THREADS=1 NAME M
cd "$M" || exit 2
DL=""
for b in Core Load SeamC SeamLoad AugC Kern Kern2 KernT KernA; do
  [ -f so/QECCount_QECCountComp_$b.so ] && DL="$DL --load-dynlib=$M/so/QECCount_QECCountComp_$b.so"
done
for so in so/QECCount_QECCountComp_Data_${NAME}_C*.so; do DL="$DL --load-dynlib=$M/$so"; done
DL="$DL --load-dynlib=$M/so/QECCount_QECCountComp_Data_${NAME}.so"
export DL
mkdir -p masks parts
N=$(cat nnear_$NAME.txt)
one() {
  i=$1
  lo=$(( N * i / NPART )); hi=$(( N * (i + 1) / NPART ))
  t0=$(date +%s)
  # shellcheck disable=SC2086
  KIND=near LO=$lo HI=$hi OUT=$M/parts/${NAME}_near_$i.txt /usr/bin/time -o "$M/parts/t_$i.txt" -f '%M' \
    "$LEAN" $DL "Mask$NAME.lean" > "$M/parts/o_$i.txt" 2>&1
  echo "part $i rc=$? $lo $hi $(( $(date +%s) - t0 )) s $(tail -1 "$M/parts/t_$i.txt") KB" >> "$M/mask_$NAME.log"
}
export -f one
export NPART N
seq 0 $((NPART - 1)) | xargs -P "$NPART" -n 1 bash -c 'one "$0"'
# shellcheck disable=SC2086
KIND=bulk LO=0 HI=100000000 OUT=$M/masks/${NAME}_bulk.txt "$LEAN" $DL "Mask$NAME.lean" >> "$M/mask_$NAME.log" 2>&1
for i in $(seq 0 $((NPART - 1))); do cat "parts/${NAME}_near_$i.txt"; done > "masks/${NAME}_near.txt"
echo "mask $NAME done $(date -u +%T): $(wc -l < masks/${NAME}_near.txt) near, $(wc -l < masks/${NAME}_bulk.txt) bulk" >> "$M/mask_$NAME.log"
