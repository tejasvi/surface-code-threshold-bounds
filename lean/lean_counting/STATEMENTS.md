# STATEMENTS: what is proved, what is assumed

Lean 4 `v4.35.0-rc3`, Mathlib `c55e6e786f49`. No `sorry`, no axioms beyond the three standard
ones (`propext`, `Classical.choice`, `Quot.sound`) and, for the native versions, the `native_decide` certificate axioms
of the check modules (listed by `#print axioms`). There are no named hypotheses: every statement below is
unconditional, given the definitions.

## Definitions a reader must trust (`QEC/Count/Defs.lean`, `QEC/Graph/Basic.lean`)

- `Vx V`: the checks (`det v`) and the two boundary vertices `b1`, `b2`; edges are `Sym2 (Vx V)`; `bd C` is the set of
  checks of odd degree in the edge set `C`; `vdeg C x` the degree of `x` in `C` (copied unchanged from an earlier formalization).
- `PrIID Eg p A = ∑_{E ⊆ Eg, A E} p^|E| (1 - p)^|Eg \ E|`: every edge of `Eg` is in the error independently with
  probability `p`.
- `IsMinCorr Eg A C`: `C ⊆ Eg`, `bd C = A`, and `|C| ≤ |C'|` for every `C' ⊆ Eg` with `bd C' = A` (minimum-weight
  decoding with uniform weights).
- `FailsB E C`: the parities of `|C ∩ δ(b1)|` and `|E ∩ δ(b1)|` differ.
- `PfailMW Eg p = PrIID Eg p (∃ C, IsMinCorr Eg (bd E) C ∧ FailsB E C)`: SOME minimum-weight correction fails, so
  the bounds hold for every tie rule.
- `PfailDec Eg p dec`: the failure probability of a decoder `dec : Finset V → Bool` (syndrome to class);
  `PfailML Eg p = ⨅ dec, PfailDec Eg p dec` (optimal = maximum-likelihood decoding).
- `BoxV n N = ∏_i Fin (N i)`; `boxEdges n N a`: pairs of checks at ℓ¹ distance `1`, half-edges from the checks with
  coordinate `a` equal to `0` to `b1`, and from those with coordinate `a` equal to `N a - 1` to `b2`.
  - `boxEdges 2 ![nx, ny] 0`: the unrotated planar code, one error sector, code capacity (checks `[0,nx) × [0,ny)`,
    rough sides at the columns `0` and `nx - 1`, code distance `nx + 1`).
  - `boxEdges 3 ![T + 1, W, H] 2`: the space-time decoding graph of the planar code (distance `H + 1`, width `W`)
    under phenomenological noise with `T` noisy rounds and a final perfect round: detectors `(t, X, Y)`, space-like
    edges = data flips, time-like edges = syndrome-bit flips, one edge per error location, all with probability `p`.
- `rhoOf ps p = √(p (1 - p) / (ps (1 - ps)))` (`QEC/Count/Final.lean`).
- The rotated surface code (`QEC/Count/RotLayout.lean`), odd distance `d`, Z errors at code capacity: qubits
  `(x, y) ∈ [0, d)²`; X checks at the plaquette positions `(i, j)` with `i + j` even, `0 ≤ i ≤ d - 2`,
  `-1 ≤ j ≤ d - 1` (`rotXCh`), each containing the qubits at the corners of its plaquette (`inCheck`); syndrome
  `rotSyn`; class `rotCls` = parity of the flips on the column `x = 0` (the support of a logical X operator);
  `IsMinCorrRot`, `FailsRot`, `PfailRot d p` (some minimum-weight correction fails), `PfailRotML d p` (optimum over
  decoders from the syndrome to the class). `PfailRot_eq` proves that this equals the failure probability of the
  region code `rotEdges d` (`QEC/Count/RotGeom.lean`) used in the proof.
- The toric code (`QEC/Count/Torus.lean`), one error sector at code capacity: checks `TorV L = Fin L × Fin L`, each
  joined to its right and upper neighbour modulo `L` (`torEdges L`, the qubits); `crV Z`, `crH Z` count the edges of
  `Z` across the vertical seam (between the columns `L - 1` and `0`) and the horizontal seam; `TrivT Z` = both counts
  even; `FailsT E C = ¬ TrivT (C ∆ E)` (the residual is homologically nontrivial); `PfailTor L p` = probability that
  some minimum-weight correction fails; `PfailTorML L p` = optimum over decoders from the syndrome to the class
  (the two crossing parities).

Modelling steps that are standard and not formalized: the identification of the code (or of the phenomenological
measurement model) with its decoding graph, and, for a square planar code, the symmetry that gives the same bound for
the other error sector (the same graph turned by a right angle). The statements are about the decoding graphs above.

## Theorems

| theorem (file) | statement | status | axioms |
|---|---|---|---|
| `QEC.planar_A6`, `planar_A6_ML` (`QEC/Thm/PlanarA6.lean`) | planar code, `0 < p ≤ 11/250`, `nx ≥ 6`: `PfailMW, PfailML ≤ ny · 2.2676 · λ^(nx-6)/(1-λ)`, `λ = 0.997 ρ(11/250, p)` | PROVED | 3 + 14 native |
| `QEC.planar_A6_kernel`, `planar_A6_kernel_ML` (`QEC/Thm/PlanarA6K.lean`) | the statement of `planar_A6`, every check evaluated by the kernel (`decide +kernel`) | PROVED | **3 standard only** |
| `QEC.planar_A8_kernel`, `planar_A8_kernel_ML` (`QEC/Thm/PlanarA8K.lean`) | planar code, `0 < p ≤ 9/200`, `nx ≥ 8`: `≤ ny · 94.47 · λ^(nx-8)/(1-λ)`, `λ = 0.995 ρ(9/200, p)`, every check evaluated by the kernel (certificate `cc2d/cert/m8g_p045`, 525 kernel modules) | PROVED | **3 standard only** |
| `QEC.planar_A10_kernel`, `planar_A10_kernel_ML` (`QEC/Thm/PlanarK10.lean`) | Theorem A, kernel-checked: the statement of `planar_A` (`p ≤ 93/2000`, `nx ≥ 10`), certificate `cc2d/cert/m10g_p0465` through the kernel route v2 (6226 kernel modules on three machines) | PROVED | **3 standard only** |
| `QEC.planar_A`, `planar_A_ML` (`QEC/Thm/Planar.lean`) | Theorem A: planar code, `0 < p ≤ 93/2000`, `nx ≥ 10`: `≤ ny · 398.91 · λ^(nx-10)/(1-λ)`, `λ = 0.998 ρ(93/2000, p)` | PROVED | 3 + 74 native (64 row ranges, 8 first steps, size, start sum) |
| `QEC.phenom_D2`, `phenom_D2_ML` (`QEC/Thm/Phenom.lean`) | Theorem D2: phenomenological, `0 < p ≤ 2/125`, `H ≥ 8`: `≤ (T+1) W · 1.2827 · λ^(H-8)/(1-λ)`, `λ = 0.998 ρ(2/125, p)` | PROVED | 3 + 110 native (96 row ranges, 12 first steps, size, start sum) |
| `QEC.phenom_D2M8_kernel`, `phenom_D2M8_kernel_ML` (`QEC/Thm/PhenomK8.lean`) | Theorem D2, kernel-checked: the statement of `phenom_D2` (`p ≤ 2/125`, `H ≥ 8`), the M = 8 certificate through the kernel route v2 (5988 kernel modules on four machines) | PROVED | **3 standard only** |
| `QEC.phenom_D2_kernel`, `phenom_D2_kernel_ML` (`QEC/Thm/PhenomK.lean`) | phenomenological, `0 < p ≤ 31/2000`, `H ≥ 6`: `≤ (T+1) W · 0.5917 · λ^(H-6)/(1-λ)`, `λ = 0.995 ρ(31/2000, p)`, every check evaluated by the kernel | PROVED | **3 standard only** |
| `QEC.rotated_S10`, `rotated_S10_ML` (`QEC/Thm/Rotated.lean`) | Theorem B (SAFE rules): rotated surface code, odd `d ≥ 11`, `0 < p ≤ 11/250`: `PfailRot, PfailRotML ≤ 2d · 212.88 · λ^(d-11)/(1-λ)`, `λ = 0.997 ρ(11/250, p)` | PROVED | 3 + 82 native (72 row ranges, 8 first steps, size, start sum) |
| `QEC.rotated_B`, `rotated_B_ML` (`QEC/Thm/RotatedB.lean`) | Theorem B: rotated surface code, odd `d ≥ 11`, `0 < p ≤ 93/2000`: `PfailRot, PfailRotML ≤ 2d · 366183771.98 · λ^(d-11)/(1-λ)`, `λ = 0.998 ρ(93/2000, p)` | PROVED | 3 + 252 native (164 near-row ranges, 8 interface and 8 bulk ranges, 70 start chunks, sizes, start sums) |
| `QEC.toric_A'_10`, `toric_A'_10_ML` (`QEC/Thm/Toric10.lean`) | Theorem A' at the M = 10 certificate: toric code, `L ≥ 1201`, `0 < p ≤ 23/500`: `PfailTor, PfailTorML ≤ L² · 428572391.6 · λ^(L-10)/(1-λ)`, `λ = 0.997 ρ(23/500, p)` | PROVED | 3 + 418 native (320 near-row ranges, 8 bulk ranges, 59 start-completeness ranges, sizes, 30 start-sum ranges) |
| `QEC.toric_A'`, `toric_A'_ML` (`QEC/Thm/Toric.lean`) | Theorem A': toric code, `L ≥ 769`, `0 < p ≤ 9/200`: `PfailTor, PfailTorML ≤ L² · 383157811 · λ^(L-8)/(1-λ)`, `λ = 0.996 ρ(9/200, p)` | PROVED | 3 + 107 native (80 near-row ranges, 8 bulk-row ranges, 13 start-completeness ranges, sizes, 5 start-sum ranges) |
| `QEC.toric_A'_kernel`, `toric_A'_kernel_ML` (`QEC/Thm/ToricK.lean`) | Theorem A', kernel-checked: the statement of `toric_A'`, certificate T8 through the kernel route for seam certificates (`QECCountComp/KernT.lean`, `QEC/Count/CertSoundTK.lean`, `QEC/Count/TorFinalK.lean`; check modules `QEC/KChecks/T8K`, 5,205 kernel modules, 225.8 core-h, on 4 machines) | PROVED | **3 standard only** |
| `QEC.rotated_B_kernel`, `rotated_B_kernel_ML` (`QEC/Thm/RotatedBK.lean`) | Theorem B, kernel-checked: the statement of `rotated_B`, certificate R10 through the kernel route for augmented certificates with packed trees (`QECCountComp/KernA.lean`, `QECCountComp/KernP.lean`, `QEC/Count/CertSoundAK.lean`, `QEC/Count/ChunksAK.lean`, `QEC/Count/ChunksP.lean`, `QEC/Count/RotFinalAK.lean`; check modules `QEC/KChecks/R10P`, 52,051 kernel modules, 7,267 core-h, on 12 machines; assembly 441 modules; sources and oleans listed in `runs/manifests/R10P_*.sha256`; 3,588 row oleans first compiled from the generator version before the row-piece change were recompiled from the current sources on 27 Oct and the assembly compiled again, with the same axioms, `runs/logs/rebuild_R10P_RN.txt`) | PROVED | **3 standard only** |
| `QEC.toric_A'_10_kernel`, `toric_A'_10_kernel_ML` (`QEC/Thm/ToricK10.lean`) | Theorem A' at 0.046, kernel-checked: the statement of `toric_A'_10`, certificate T10 through the kernel route for seam certificates with packed trees (`QECCountComp/KernT.lean`, `QECCountComp/KernP.lean`, `QEC/Count/CertSoundTK.lean`, `QEC/Count/ChunksTK.lean`, `QEC/Count/ChunksP.lean`, `QEC/Count/TorFinalK.lean`; check modules `QEC/KChecks/T10P`, 97,435 kernel modules, 15,236 core-h, on 14 machines; assembly 764 modules; sources and oleans listed in `runs/manifests/T10P_*.sha256`) | PROVED | **3 standard only** |

`ρ(ps, p) = rhoOf ps p = √(p (1 - p) / (ps (1 - ps)))`; so `λ` is `0.997`, `0.998`, `0.998`, `0.997` resp. `0.996`
times `ρ ≤ 1`, and `λ < 1` for every `p ≤ p**`. The code distance is `nx + 1` (A6, A), `d = H + 1` (D2;
`λ^(H-8) = λ^(d-9)`) and `L` (A'). Native checks (one core per module, 26 Oct 2026): A6 13 modules ~1 min;
A10 73 modules ~18 CPU-min; D2 109 modules ~27 CPU-min; S10 81 modules ~33 CPU-min; T8 106 modules ~17 CPU-min;
at most ~0.84 GB per process. Kernel checks of A6K: 73 modules, 0.21 core-h, at most 6.1 GB per process (rerun
after the last change of `Kern.lean`). Kernel checks of D2K6 (`d2/out/m6.states`,
`d2/cert/m6_p0155.H`, hints `d2/out/m6.trans`; cb612c06…, 943938b9…, 83237b58…): 401 modules (256 row ranges, 144
start chunks by two first steps, size and start sum), 140 on a workstation and 261 on a larger machine, about 5 core-h, at most
28 GB (start sum) and 11 GB (rows) per process.

The kernel route (`QECCountComp/Kern.lean`, `QEC/Count/CertSoundK.lean`, `QEC/Count/FinalK.lean`) stores the listed
states in a tree of (key, `H`, mask) and finds matchings by recursion; the mask (the candidates whose full window the
generator excluded) is only a hint: each claimed exclusion is re-found and checked by `checkW` inside the kernel.

Theorem B (augmented): the region-aware witness check `checkWA` (`QECCountComp/AugC.lean`) tests a window at
the height of its first vertex below the top smooth side: the alternative stays below the top side, and with the strict
bottom side (`hN = 0`) it never goes below the window's least `U - V`, so it stays in the smooth strip for every `d`
(`RotSoundA`; the note's `d ≥ 45` is not needed). States within `HC = 24` of the top carry their exact head height
(potentials `G`); far states use the bulk potential, checked at one far height and at the interface height
(`CertSoundA`; heights do not wrap). Counting with height-dependent exclusions (`CountingT` with `nxtA`), assembly
(`RotAssemblyA`), scaling (`RotFinalA`). `checkWA` and its searches reproduce the certificate generator `tm2d_aug_omp` exactly on
test certificates (M = 4..8; every row's successors, 3,100,345 rows at M = 8; mutants rejected). Native checks of R10:
251 modules (13.9 core-h, at most 5.6 GB per process).

Theorem A' (toric code): the tie-break is `φ = x_rep` (`phiTor`), the column in `[0, L)`, which jumps at the
vertical seam. A window is tested at the seam offset of its first vertex (`qoffZ`: the column taken in `[-L/2, L/2)`)
by the seam witness check `checkWT` (`QECCountComp/SeamC.lean`): `Φ = L·A + B` is compared lexicographically and
`|ΔB| < L0` is checked, so a passing check holds for every `L ≥ L0` (`TorSound`: no window of a failure cycle is
excluded). States near the seam carry their head offset (`-HC ≤ o < HC`, potentials `G`); far states use the bulk
potential; windows of far states lie on one side of the seam, where the check does not depend on the offset
(`SeamShift`), so the bulk rows at one far offset and the two interface rows cover all far states (`CertSoundT`).
Counting with offset-dependent exclusions (`CountingT`), the failure cycle of length `≥ L` from each start vertex
with one closing edge (`TorAssembly`, `TorWalk`), all `p ≤ 9/200` by scaling (`TorFinal`). The seam check reproduces
the certificate generator `tm2d_seam` exactly on test certificates (`T4`, `T5`: every row's successor count; mutants rejected).
The constant `383157811` includes the closing-edge factor `ω_E + ω_C` and is the maximum over the start offsets.

The rotated code at `p ≤ 0.044` (SAFE rules) is proved above: region codes with one outer point per half-edge
(`RDefs`, `RDecoder`), the SAFE witnesses (two alternatives with `x - y` in `[lo, hi + 1]` resp. `[lo - 1, hi]`,
`QECCountComp/Safe.lean`, `CertSoundS`), the soundness in the rotated region (`RotSound`: the witness inside the
smooth strip; edges beyond a rough line dropped), the assembly (`RotAssembly`, `RotFinal`).

## The proof (all proved, standard axioms only)

- `QEC/Count/IID.lean`: monotonicity, union bound, `Pr(E ∩ γ = S) = p^|S| (1-p)^|γ \ S|`, the tilt, `PfailML ≤ PfailMW`.
- `QEC/Count/Decoder.lean`: a failing minimizer of least `Φ` exists; the failure path; half-weight; the exchange lemma
  (rules (M), (J), (P_M), (P_J), (S) in one statement).
- `QEC/Count/BoxGeom.lean`, `BoxSound.lean`: positions, adjacency as unit steps, the pattern of a path; no window of
  the failure path is excluded by a checked witness (box domination: the alternative lies in the window's bounding
  box, hence in the box).
- `QEC/Count/Counting.lean`: counting legal labelled walks with memory `K` from rows of a potential.
- `QEC/Count/CertSound.lean`: the certificate checks of the computational core imply the counting hypotheses.
- `QEC/Count/Assembly.lean`: `pfail_box_le`; `QEC/Count/Final.lean`: `box_bound_of_cert` (all `p ≤ p**` by scaling).
- Rotated code: `CountingX`, `CertSoundS`, `RDefs`, `RDecoder`, `RotGeom`, `RotSound`, `RotLayout`, `RotAssembly`,
  `RotFinal`; augmented (Theorem B): `AugDefs`, `RotSoundA`, `CertSoundA`, `RotAssemblyA`, `ChunksA`,
  `RotFinalA`. Toric code: `Torus`, `TorDefs`, `TorSound`, `CountingT`, `SeamShift`, `CertSoundT`, `TorWalk`,
  `TorAssembly`, `ChunksT`, `TorFinal`.

## Trusted computing base

- The Lean kernel. For the native versions also the Lean compiler and runtime: the certificate checks of
  `QECCountComp/Core.lean` (and `Safe.lean`, `SeamC.lean`, `AugC.lean`) run as compiled code (`precompileModules`,
  loaded with `--load-dynlib`) inside `native_decide`, on a workstation or a larger machine (same Lean toolchain, same OS and
  glibc; check oleans copied back). The witness searches `findW`, `findWS`, `findWT`, `findWA` are untrusted (only
  their outputs, checked by `checkW`, `checkWS`, `checkWT`, `checkWA`, are used).
- Data (untrusted; a wrong value can only make a check fail): `QECCountComp/Data/<name>.lean` records the sha256 of
  the generator files it was made from:
  - A6: `cc2d/cert/m6g_p044.{states,H}` (66b84e4d…, 6d5c5877…);
  - A10: `cc2d/cert/m10g_p0465.{states,H}` (0c7081d4…, b6efc5e8…);
  - D2: `d2/out/m8.states`, `d2/cert/m8_p016.H` (c9d2bda6…, d71d975f…);
  - S10: `cc2d/cert/s10_p044.{states,H}` (922851ed…, d16d6aca…);
  - T8: `cc2d/seam/s8_p045.{json,near_keys,seam_H,bulk_states}` (a2afbce5…, e8437162…, e8948d95…,
    86f1304d…), output of `tm2d_seam.cpp` (24c9d856…);
  - R10: `cc2d/rot10/r10_p0465.{json,near_keys,aug_H,bulk_states}` (c3c5fc40…, fd4488c2…, 2ac16544…,
    0c7081d4…), output of `tm2d_aug_omp.cpp` (4f49ae21…);
  - T10: `t10_p046.{json,near_keys,seam_H,bulk_states}` (32ca9cfc…, 6535eb3e…, 6ca57443…, 818d3546…),
    output of `tm2d_seam.cpp` (24c9d856…) at M = 10 (copy in `cc2d/seam10/`); data generated by
    `gen/mkseam2.py` (streaming, external merge sort; reproduces `gen/mkseam.py` exactly on T5).
- Kernel data (`QECCountComp/KData/<name>.lean` records the sha256 of its inputs; the transition files give only the
  claimed exclusions, each checked again in the kernel):
  - KA8: `cc2d/cert/m8g_p045.{states,H,trans}` (b94e10da…, d5b253c1…, 1dca48cf…);
  - A10K2: `cc2d/cert/m10g_p0465.{states,H,trans}` (0c7081d4…, b6efc5e8…, 47601481…);
  - D2K6: `d2/out/m6.states`, `d2/cert/m6_p0155.H`, `d2/out/m6.trans` (cb612c06…, 943938b9…, 83237b58…);
  - D2M8K2: `d2/out/m8.states`, `d2/cert/m8_p016.H`, `d2/out/m8.trans` (c9d2bda6…, d71d975f…, 71eccc04…).

Labels: the native_decide theorems (planar_A6, planar_A, phenom_D2, rotated_S10, rotated_B, toric_A', toric_A'_10)
depend on the Lean compiler as well as the kernel; the kernel-only theorems (planar_A6_kernel, planar_A8_kernel,
planar_A10_kernel, phenom_D2_kernel, phenom_D2M8_kernel, toric_A'_kernel, rotated_B_kernel, toric_A'_10_kernel)
depend on the kernel alone. Theorems A, D2 and B at their headline values, and A' at 0.045 and at 0.046, are therefore
proved twice: natively (planar_A, phenom_D2, rotated_B, toric_A', toric_A'_10) and kernel-only (planar_A10_kernel,
phenom_D2M8_kernel, rotated_B_kernel, toric_A'_kernel, toric_A'_10_kernel), from the same certificates.
The distributed builds were checked across machines: every machine's kernel data sources and oleans are byte-identical
(`runs/khash/`), because imported theorems are not rechecked and a check olean names the data without containing it.

Kernel data of A10K2 and D2M8K2 (subtree constants, 287 MB and 384 MB of Lean source) are regenerated by
`gen/mkkdata2.py` (member sha256 of the generated sources in `archive/*_kdata.sha256`); their oleans (6.5 GB,
9 GB) and the check oleans were built on the machine where the assembly and the theorems were compiled (logs
`runs/logs/kasmP_*`).
