#!/usr/bin/env bash
# run_maskT8.sh KIND LO HI OUT: masks of T8 entries [LO, HI) with compiled evaluation (one core, guarded)
cd "$(dirname "$0")/.." || exit 2
L=.lake/build/lib/lean
DL="--load-dynlib=$L/QECCount_QECCountComp_Core.so --load-dynlib=$L/QECCount_QECCountComp_Load.so"
DL="$DL --load-dynlib=$L/QECCount_QECCountComp_SeamC.so --load-dynlib=$L/QECCount_QECCountComp_SeamLoad.so"
DL="$DL --load-dynlib=$L/QECCount_QECCountComp_Kern.so --load-dynlib=$L/QECCount_QECCountComp_Kern2.so"
DL="$DL --load-dynlib=$L/QECCount_QECCountComp_KernT.so"
for so in $L/QECCount_QECCountComp_Data_T8_C*.so; do DL="$DL --load-dynlib=$so"; done
DL="$DL --load-dynlib=$L/QECCount_QECCountComp_Data_T8.so"
KIND=$1 LO=$2 HI=$3 OUT=$4 CAP=0.2 bash scripts/chk.sh lean $DL .tmp/MaskT8.lean
