#!/usr/bin/env bash
# box_khash.sh OUT: on a build machine, in $KT_DIR: the sha256 of the kernel data oleans of OUT
# (lib/QECCountComp/KData/OUT.olean and lib/QECCountComp/KData/OUT/*.olean) into kdata_OUT.sha256, and of their
# generated sources (QECCountComp/KData/OUT.lean and QECCountComp/KData/OUT/*.lean) into kdata_OUT_src.sha256, each
# sorted by path. The check modules of a certificate are compiled on several boxes against their own kernel data
# builds, and the assembly imports them together with one box's build; Lean does not recheck imported theorems, and a
# check olean names the data without containing it, so the data sources and oleans must agree across the boxes.
set -euo pipefail
OUT=$1
cd "$KT_DIR"
for kind in olean src; do
  if [ $kind = olean ]; then d=lib/QECCountComp/KData; x=olean; f=kdata_$OUT.sha256
  else d=QECCountComp/KData; x=lean; f=kdata_${OUT}_src.sha256; fi
  { echo "$d/$OUT.$x"; find "$d/$OUT" -name "*.$x"; } | LC_ALL=C sort | xargs sha256sum > "$f.tmp"
  mv "$f.tmp" "$f"
  echo "kdata $OUT $kind: $(wc -l < "$f") files, list sha256 $(sha256sum "$f" | cut -c1-16)"
done
