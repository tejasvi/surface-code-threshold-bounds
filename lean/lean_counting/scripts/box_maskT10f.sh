#!/usr/bin/env bash
# box_maskT10f.sh NPART: on a build machine (inside one job): the exclusion hints of the seam certificate T10 by compiled
# evaluation, from the copy $KM_DIR (lib = core oleans with KernT and the T10 data oleans, so =
# their shared libraries, MaskT10.lean): near entries in NPART parts in parallel, then the bulk entries; output in
# km10/masks. Log: km10/mask_T10.log.
set -uo pipefail
NPART=$1
M=${KM_DIR:?set KM_DIR to the hint workspace}
export LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
export LEAN_PATH=$M/lib LEAN_NUM_THREADS=1 M NPART
cd "$M" || exit 2
DL=""
for b in Core Load SeamC SeamLoad Kern Kern2 KernT; do DL="$DL --load-dynlib=$M/so/QECCount_QECCountComp_$b.so"; done
for so in so/QECCount_QECCountComp_Data_T10_C*.so; do DL="$DL --load-dynlib=$M/$so"; done
DL="$DL --load-dynlib=$M/so/QECCount_QECCountComp_Data_T10.so"
export DL
mkdir -p masks parts
N=157107748
export N
one() {
  i=$1
  lo=$(( N * i / NPART )); hi=$(( N * (i + 1) / NPART ))
  t0=$(date +%s)
  # shellcheck disable=SC2086
  KIND=near LO=$lo HI=$hi OUT=$M/parts/T10_near_$i.txt /usr/bin/time -o "$M/parts/t_$i.txt" -f '%M' \
    "$LEAN" $DL MaskT10.lean > "$M/parts/o_$i.txt" 2>&1
  echo "part $i rc=$? $lo $hi $(( $(date +%s) - t0 )) s $(tail -1 "$M/parts/t_$i.txt") KB" >> "$M/mask_T10.log"
}
export -f one
seq 0 $((NPART - 1)) | xargs -P "$NPART" -n 1 bash -c 'one "$0"'
# shellcheck disable=SC2086
KIND=bulk LO=0 HI=100000000 OUT=$M/masks/T10_bulk.txt "$LEAN" $DL MaskT10.lean >> "$M/mask_T10.log" 2>&1
for i in $(seq 0 $((NPART - 1))); do cat "parts/T10_near_$i.txt"; done > masks/T10_near.txt
echo "mask T10 done $(date -u +%T): $(wc -l < masks/T10_near.txt) near, $(wc -l < masks/T10_bulk.txt) bulk" >> "$M/mask_T10.log"
