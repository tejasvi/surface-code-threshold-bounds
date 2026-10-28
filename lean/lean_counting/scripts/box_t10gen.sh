#!/usr/bin/env bash
# box_t10gen.sh: on a build machine, in $KT_DIR (inputs/t10 = the t10_p046 certificate files, masks from
# the hint workspace km10): regenerate the compiled-evaluation data of T10 (gen/mkseam2.py, as for the compiled run; member sha256
# compared with archive/T10_chunks.sha256), generate the packed kernel certificate T10P (gen/mkkseam.py: leaves of at
# most 2048 records, rows in 4 pieces, start modules of 64 prefixes of depth 5, 2 leaves per row module), and pack its
# sources into T10P_src.tar.zst for the other machines. Log: t10gen.log.
set -euo pipefail
K=${KT_DIR:?set KT_DIR to the kernel-route work directory}
cd "$K"
echo "[t10gen] $(date -u -Is) mkseam2"
NPROC=20 python3 -I -B gen/mkseam2.py T10 inputs/t10/t10_p046 10 320 8 1 400000 2 "$K/.t10sort" > logs_mkseam2_T10.json
( cd QECCountComp/Data && sha256sum T10/C*.lean | sort -k2 ) > t10_chunks_check.sha256
sort -k2 archive/T10_chunks.sha256 > t10_chunks_ref.sha256
if cmp -s t10_chunks_check.sha256 t10_chunks_ref.sha256; then echo "[t10gen] chunks identical to the compiled run"; else echo "[t10gen] CHUNKS DIFFER"; exit 3; fi
cp ../km10/masks/T10_near.txt ../km10/masks/T10_bulk.txt masks/
echo "[t10gen] $(date -u -Is) mkkseam"
PACK=1 LEAF=2048 CHUNK=4 EGRP=2 python3 -I -B gen/mkkseam.py T10 T10P masks 5 2 200 > gen_T10P.json
echo "[t10gen] $(date -u -Is) pack"
tar cf - QECCountComp/KData/T10P QECCountComp/KData/T10P.lean QEC/KChecks/T10P | zstd -T16 -q > T10P_src.tar.zst
sha256sum T10P_src.tar.zst > T10P_src.sha256
echo "[t10gen] $(date -u -Is) done $(du -h T10P_src.tar.zst | cut -f1) $(cut -c1-16 T10P_src.sha256)"
