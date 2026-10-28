# QECML: Lean proofs for the optimal threshold of the planar surface code

This Lean 4 project contains the formal proofs of the certified-threshold theorem of the paper. For the planar surface
code with independent bit flips (one error sector), it bounds the failure probability of maximum-likelihood decoding
and shows that the optimal threshold is at least 0.100, under conditions (V6), (Hcov) and (Bin) of the paper, with
confidence 1 - 2e-9. Lean checks the bound only at the registered parameters: bad-block level 5e-4, level parameter
a1 = 12 and window radius R = L - 1.

## Build

Requirements: elan (the Lean toolchain manager). From the project root:

    bash scripts/build.sh

This downloads the prebuilt Mathlib, builds the library and prints the axioms of the main theorems, each of which
depends on `propext`, `Classical.choice` and `Quot.sound` at most. Lean version: 4.35.0-rc3 (`lean-toolchain`);
Mathlib: commit c55e6e786f49 (`lake-manifest.json`). The library has 65 modules under `QECML/`. It contains no
`sorry`, no `axiom` declaration and no `native_decide`.

## Main theorems

- `QECML.theoremB_a12_main`, `QECML.threshold_a12_main` (`QECML/TwoD/HeadlineMain.lean`): the bound on the optimal
  failure probability and the threshold, from (V6) (`S3Prog.V6`), (Hcov) (`S3Fam.Hcov`), `R = L - 1`, `L ≥ 2`, and the
  bound 5e-4 on the five bad-block probabilities at `p = 0.100` (`S3Fam.Hstat`).
- `QECML.theoremB_certified`, `QECML.theoremB_certified_familywise` (`QECML/TwoD/HeadlineCert.lean`): the confidence
  statement. The binomial model of the counts, condition (Bin), is the hypothesis `hlaw`; no bound on the bad-block
  probabilities is assumed.
- `QECML.obs_accept`, `QECML.obs_cp`, `QECML.cp_upper_k*`, `QECML.cp_tight_k*` (`QECML/TwoD/CertObserved.lean`): the
  accepted counts satisfy the acceptance rule, and the quoted Clopper–Pearson upper bounds are valid and correctly
  rounded up.
- `QECML.d1_accept`, `QECML.d1_cp`, `QECML.d1_cp_upper_k4` and related lemmas (`QECML/D1Observed.lean`): the counts of
  the certificate under measurement errors. They support a remark in the paper's discussion; the deduction from that
  certificate to a threshold is not formalized.

`scripts/Axioms.lean` lists these theorems and the lemmas they rest on.

## Names in the sources

- Theorem B is the bound on the optimal failure probability. Theorem A, a named hypothesis in early modules, is the
  failure bound of the auxiliary decoder.
- S3 and S3' denote the auxiliary (windowed) decoder; its stage 1 is the registered program.
- The 2D lemma is the failure bound of the auxiliary decoder, with its T1 and T2 terms. It is proved for the registered
  parameters with the constants `2e4`, `0.02` in the second term (`QECML/TwoD/HeadlineFull.lean`).
- Lemmas A, B, C, X and (W0, W1, R) are the steps (A), (B), (C), (X) and (W) of the proof outlined in the paper and
  written out in its Supplement S1.
- `S3Prog.V6` and `S3Fam.Hcov` are conditions (V6) and (Hcov); the paper's validations V2, V4 and V6 test them.
- Design A is the registered acceptance rule: `n = 1.2e5` samples per type, accept iff at most 18 are bad.
