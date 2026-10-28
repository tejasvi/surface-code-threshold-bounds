# lean_count: Lean 4 formalization of the counting bounds

This tree proves, in Lean 4 with Mathlib, the threshold bounds of the paper by labelled-path counting with exact
integer certificates: Theorem A (planar code), Theorem B (rotated code), Theorem A' (toric code, at 0.045 and 0.046)
and Theorem D2 (phenomenological noise), each as a statement about the failure probability of minimum-weight and of
maximum-likelihood decoding. `STATEMENTS.md` lists every final theorem with its statement, file, status and axioms,
and the certificate files with their sha256.

## Toolchain

- Lean: `lean-toolchain` (`leanprover/lean4:v4.35.0-rc3`).
- Mathlib: `lake-manifest.json` (rev `c55e6e786f49471c72fbddbec5415808896aec1e`, input rev `v4.35.0-rc3`), with its
  dependencies pinned there.
- Python 3 for the certificate generators in `gen/` (standard library only).

## Building the general argument

```
lake exe cache get            # Mathlib oleans
lake build $(ls QEC/Count/*.lean QEC/Graph/*.lean QECCountComp/*.lean | sed 's/\.lean$//; s#/#.#g')
```

These 63 modules are the definitions and theorems of the general argument (probability estimates, decoder lemmas,
counting lemmas, soundness of the certificate checks, assembly and scaling) and the check functions. Elaborated one
module at a time with plain `lean -o` on one core: 271 s in total, at most 2.7 GB per module; `lake build` also
compiles the `QECCountComp` modules to native code (`precompileModules`, needed by `native_decide`), which adds to
this. `runs/logs/remeasure_lib.txt` has an earlier measurement of 53 of these sources: 310 s of processor time, at
most 3.0 GB. Each theorem file then elaborates in less than half a minute (`runs/logs/remeasure_thm.txt`), once its
certificate's check modules are built.

## Final theorems and their axioms

| Theorem | File | Axioms |
|---|---|---|
| `planar_A`, `planar_A_ML` (Theorem A, `p ≤ 0.0465`) | `QEC/Thm/Planar.lean` | 3 standard + 74 `native_decide` |
| `planar_A10_kernel`, `planar_A10_kernel_ML` (same statement) | `QEC/Thm/PlanarK10.lean` | 3 standard only |
| `rotated_B`, `rotated_B_ML` (Theorem B, `p ≤ 0.0465`) | `QEC/Thm/RotatedB.lean` | 3 standard + 252 `native_decide` |
| `rotated_B_kernel`, `rotated_B_kernel_ML` (same statement) | `QEC/Thm/RotatedBK.lean` | 3 standard only |
| `toric_A'`, `toric_A'_ML` (Theorem A', `p ≤ 0.045`) | `QEC/Thm/Toric.lean` | 3 standard + 107 `native_decide` |
| `toric_A'_kernel`, `toric_A'_kernel_ML` (same statement) | `QEC/Thm/ToricK.lean` | 3 standard only |
| `toric_A'_10`, `toric_A'_10_ML` (Theorem A', `p ≤ 0.046`) | `QEC/Thm/Toric10.lean` | 3 standard + 418 `native_decide` |
| `toric_A'_10_kernel`, `toric_A'_10_kernel_ML` (same statement) | `QEC/Thm/ToricK10.lean` | 3 standard only |
| `phenom_D2`, `phenom_D2_ML` (Theorem D2, `p ≤ 0.016`) | `QEC/Thm/Phenom.lean` | 3 standard + 110 `native_decide` |
| `phenom_D2M8_kernel`, `phenom_D2M8_kernel_ML` (same statement) | `QEC/Thm/PhenomK8.lean` | 3 standard only |
| `planar_A6`, `planar_A6_ML`; `rotated_S10`, `rotated_S10_ML` | `QEC/Thm/PlanarA6.lean`, `Rotated.lean` | 3 standard + 14 resp. 82 `native_decide` |
| `planar_A6_kernel`, `planar_A8_kernel`, `phenom_D2_kernel` (and `_ML`) | `QEC/Thm/PlanarA6K.lean`, `PlanarA8K.lean`, `PhenomK.lean` | 3 standard only |

The three standard axioms are `propext`, `Classical.choice` and `Quot.sound`. A `native_decide` axiom records a check
that was evaluated by compiled code; the kernel-only theorems have every check reduced by the Lean kernel
(`decide +kernel`). The `#print axioms` outputs are in `runs/logs/axioms_<file>.out`.

## Certificates and generated modules

The certificate files (state lists, potentials, transition hints, seam and augmented certificates) are not part of
this tree; `STATEMENTS.md` gives their names (relative to the certificate package) and sha256. The data, kernel data
and check modules of the large certificates are generated from them by the programs in `gen/` and are not shipped
either; the smaller kernel certificates (`QEC/KChecks/A6K`, `A6K2`, `KA8`, `D2K6`, `A10K2`, `D2M8K2`, `T8K`) ship
their check and assembly sources. With `IN` the directory of the certificate files:

```
# native checks (compiled evaluation)
python3 -I -B gen/mkdata.py A10 IN/m10g_p0465.states IN/m10g_p0465.H 2 9 1,9 93 2000 3091 1000 499 500 100 64
python3 -I -B gen/mkall.py A10 93 2000 3091 1000
python3 -I -B gen/mkdata.py D2 IN/out/m8.states IN/cert/m8_p016.H 3 7 81,1,9 2 125 231 50 499 500 10000 96
python3 -I -B gen/mkall.py D2 2 125 231 50
python3 -I -B gen/mkseam.py T8 IN/s8_p045 10 80 8 4 400000 12;  python3 -I -B gen/mkseamall.py T8
python3 -I -B gen/mkaug.py R10 IN/r10_p0465 100 164 8 8 1 dfsSplit=2;  python3 -I -B gen/mkaugall.py R10
NPROC=20 python3 -I -B gen/mkseam2.py T10 IN/t10_p046 10 320 8 1 400000 2 TMPDIR;  python3 -I -B gen/mkseamall.py T10
# kernel checks
python3 -I -B gen/mkkdata2.py A10K2 IN/m10g_p0465.states IN/m10g_p0465.H IN/m10g_p0465.trans 2 9 1,9 93 2000 3091 1000 499 500 100 4 4 4 100
python3 -I -B gen/mkkdfs2.py A10K2 2 5;  python3 -I -B gen/mkkall2.py A10K2
python3 -I -B gen/mkkdata2.py D2M8K2 IN/out/m8.states IN/cert/m8_p016.H IN/out/m8.trans 3 7 81,1,9 2 125 231 50 499 500 10000 3 4 2 100
python3 -I -B gen/mkkdfs2.py D2M8K2 3 4;  python3 -I -B gen/mkkall2.py D2M8K2
python3 -I -B gen/mkkseam.py T8 T8K .tmp/masks 3 8 200;  ALAYOUT=chain python3 -I -B gen/mkkallTA.py T8K
PACK=1 LEAF=2048 CHUNK=4 EGRP=2 python3 -I -B gen/mkkaug.py R10 R10P masks 5 2 200;  python3 -I -B gen/mkkallTA.py R10P
PACK=1 LEAF=2048 CHUNK=4 EGRP=2 python3 -I -B gen/mkkseam.py T10 T10P masks 5 2 200
python3 -I -B gen/mkkE.py T10P 6 3;  python3 -I -B gen/mkkallTA.py T10P
```

The seam and augmented kernel certificates (`T8K`, `R10P`, `T10P`) also read hint files (claimed exclusion masks,
re-checked by the kernel). They are made by compiled evaluation of `gen/MaskT.lean.in` and `gen/MaskA.lean.in`
(`scripts/run_maskT8.sh`; `scripts/box_mask.sh`, `box_maskT10f.sh` and `box_maskbulk.sh`); their sha256 are listed in
`archive/masks.sha256` and recorded in the kernel data roots (`QECCountComp/KData/T8K.lean`, `R10P.lean`,
`T10P.lean`). The generators are deterministic: `runs/manifests/R10P_sources.sha256` and `T10P_sources.sha256` list
every generated source, `R10P_oleans.sha256`, `T10P_oleans.sha256` and `T8K_check_oleans.sha256` every olean, and
`archive/*_kdata.sha256` the kernel data sources of A10K2 and D2M8K2.

## Re-checking a kernel theorem

1. Generate the data and the kernel certificate with the commands above and compare the sources with the manifests.
2. Build the kernel data, compile the check modules and the assembly, then the theorem file:
   `scripts/box_ktbuild.sh`, `box_ktrun.sh`, `box_ktasm.sh` (seam and augmented certificates; one job on a large
   machine, `KT_DIR` the work directory, `LC_DIR` a lake-built copy of this tree), or `scripts/run_kchecks.sh`,
   `box_krun2.sh` and `box_kassemble.sh` for A10K2 and D2M8K2. Each check module is one `lean` process with one
   thread; the module counts, processor time and memory of our runs are in `STATEMENTS.md` and `runs/logs/`
   (from 5,205 modules and about 226 core-hours for T8K to 97,435 modules and about 15,200 core-hours for T10P).
3. When the checks are spread over several machines, check that every machine's kernel data oleans are identical
   (`scripts/box_khash.sh`; our lists in `runs/khash/`, machines labelled `n00`-`n22`), and that they are what the
   current sources compile to (`scripts/box_kdata_recheck.sh`): imported theorems are not checked again.
4. `#print axioms` on the theorems of the theorem file must give the three standard axioms only.

### R10P and T10P, step by step

The work directory `KT_DIR` holds copies of this tree's `gen/`, `scripts/` and `QEC/Thm/`, the oleans of the general
argument (from `lake build` above) in `KT_DIR/lib`, the compiled-evaluation data of R10 resp. T10 in
`QECCountComp/Data/` (generated from the certificate files by `gen/mkaug.py` resp. `gen/mkseam2.py`, commands above)
and the hint files in `masks/`. `LC_DIR` is a lake-built copy of this tree (its `.lake/packages` give Mathlib).
The manifests use paths relative to `KT_DIR`.

```
cd $KT_DIR
# generate the kernel certificate and check every generated source
PACK=1 LEAF=2048 CHUNK=4 EGRP=2 python3 -I -B gen/mkkaug.py R10 R10P masks 5 2 200
python3 -I -B gen/mkkallTA.py R10P
sha256sum -c --quiet $TREE/runs/manifests/R10P_sources.sha256
# build the kernel data, the check modules and the assembly; elaborate the theorem file with #print axioms
bash scripts/box_ktbuild.sh R10P 300
bash scripts/box_ktrun.sh R10P QEC/KChecks/R10P/LIST.txt 130
bash scripts/box_ktasm.sh R10P 128 RotatedBK
sha256sum -c --quiet $TREE/runs/manifests/R10P_oleans.sha256
```

For T10P the generation is `PACK=1 LEAF=2048 CHUNK=4 EGRP=2 python3 -I -B gen/mkkseam.py T10 T10P masks 5 2 200`,
then `python3 -I -B gen/mkkE.py T10P 6 3` (start modules of 512 depth-6 prefixes) and
`python3 -I -B gen/mkkallTA.py T10P`, checked against `T10P_sources.sha256`. The build is the same with `T10P` and
`ToricK10`, checked against `T10P_oleans.sha256`. `box_ktrun.sh` takes any sublist of `LIST.txt`, so the check
modules can be spread over several machines (`box_kfleet_job.sh` computes one machine's share). The parallelism
above suits a machine with 384 hardware threads and 2.9 TB of memory: R10P row modules peak at 13.4 GB, start modules
at 43.4 GB; T10P modules at 23.1 GB. `#print axioms` output lands in `thm_RotatedBK.out` resp. `thm_ToricK10.out`.

The native theorems are re-checked the same way with `scripts/run_checks.sh` (`run_checks_aug.sh` for R10), which
loads the compiled check functions and data (`--load-dynlib`) so that `native_decide` runs compiled code.

## Run records

- `runs/logs/`: one line per check or assembly module ("MODULE STATUS SECONDS MAXRSS_KIB"); `README.txt` there.
- `runs/manifests/`: sha256 of the generated sources and of the oleans (see above). `R10P_stale_RN.sha256` lists
  the 3,664 R10P row oleans compiled before a rewrite of the row sources and replaced by recompiled ones (3,588 of
  them came from the earlier generator version; `runs/logs/rebuild_R10P_RN.txt`, `kchecks_R10P.rebuild.log`,
  `kasm_R10P.rebuild.log`); `R10P_oleans.sha256` lists the oleans in use.
- `runs/khash/`: per-machine sha256 lists of the kernel data sources and oleans.
- `runs/tguard_R10P.tsv`, `runs/tguard_T10P.tsv`, `runs/tguard/`: the modules whose timeout a watcher held near the
  7,200 s limit (`scripts/box_tguard.sh`); each counted as passed only after its `lean` process exited with status 0
  and wrote its olean.

## Changes for this release

This tree is the development tree with comments, documentation, scripts and run records adjusted; no Lean
declaration changed.

- Doc comments of 15 Lean files (`QEC/Count/Counting.lean`, `QEC/Count/OddEdges.lean`, `QECCountComp/AugC.lean` and
  the theorem files `QEC/Thm/PhenomK.lean`, `PhenomK8.lean`, `PlanarA6K.lean`, `PlanarA8K.lean`, `PlanarK10.lean`,
  `Rotated.lean`, `RotatedB.lean`, `RotatedBK.lean`, `Toric.lean`, `Toric10.lean`, `ToricK.lean`, `ToricK10.lean`):
  certificate sources and machines are named generically. With comments removed, each file is identical to its
  development version; the 63 modules of the general argument give the same declarations (types and values) as the
  development build, and so do the theorems of the theorem files. Their oleans differ in the stored doc strings.
- Scripts: machine-specific paths are environment variables (`KT_DIR`, `LC_DIR`, `LC2_DIR`, `KM_DIR`, `RESULTS`);
  the core-hour guard (`GUARD`) and the core picker (`PICK_CORE`) are optional.
- Run records: machines are labelled `n00`-`n22`; job names and paths were removed from two log lines.
- Not included: scripts that only moved files between machines or controlled the jobs, internal run lists, developer
  tests that read or write local absolute paths or need test certificates not in this tree, and scratch files.
