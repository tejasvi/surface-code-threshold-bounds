#!/usr/bin/env bash
# box_maskbulk.sh DIR NAME NBULK NPART: on a build machine (inside one job), in the hint workspace DIR (km for R10 with
# box_mask.sh's layout, km10 for T10 with box_maskT10f.sh's): the bulk-entry hints of NAME in NPART parts in parallel
# (NBULK bulk entries), then the near and bulk parts concatenated into DIR/masks/NAME_{near,bulk}.txt. Log:
# DIR/maskbulk_NAME.log.
set -uo pipefail
M=$1; NAME=$2; NB=$3; NPART=$4
export LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
export LEAN_PATH=$M/lib LEAN_NUM_THREADS=1 M NAME NB NPART
cd "$M" || exit 2
DL=""
for b in Core Load SeamC SeamLoad AugC Kern Kern2 KernT KernA; do
  [ -f "so/QECCount_QECCountComp_$b.so" ] && DL="$DL --load-dynlib=$M/so/QECCount_QECCountComp_$b.so"
done
for so in so/QECCount_QECCountComp_Data_${NAME}_C*.so; do DL="$DL --load-dynlib=$M/$so"; done
DL="$DL --load-dynlib=$M/so/QECCount_QECCountComp_Data_${NAME}.so"
export DL
mkdir -p masks partsb
one() {
  i=$1
  lo=$(( NB * i / NPART )); hi=$(( NB * (i + 1) / NPART ))
  t0=$(date +%s)
  # shellcheck disable=SC2086
  KIND=bulk LO=$lo HI=$hi OUT=$M/partsb/${NAME}_bulk_$i.txt "$LEAN" $DL "Mask$NAME.lean" > "$M/partsb/o_$i.txt" 2>&1
  echo "bulk part $i rc=$? $lo $hi $(( $(date +%s) - t0 )) s" >> "$M/maskbulk_$NAME.log"
}
export -f one
seq 0 $((NPART - 1)) | xargs -P "$NPART" -n 1 bash -c 'one "$0"'
np=$(ls parts | command grep -c "^${NAME}_near_[0-9]*\.txt$")
for i in $(seq 0 $((np - 1))); do cat "parts/${NAME}_near_$i.txt"; done > "masks/${NAME}_near.txt"
for i in $(seq 0 $((NPART - 1))); do cat "partsb/${NAME}_bulk_$i.txt"; done > "masks/${NAME}_bulk.txt"
echo "maskbulk $NAME done $(date -u +%T): $(wc -l < "masks/${NAME}_near.txt") near ($np parts), $(wc -l < "masks/${NAME}_bulk.txt") bulk" >> "$M/maskbulk_$NAME.log"
