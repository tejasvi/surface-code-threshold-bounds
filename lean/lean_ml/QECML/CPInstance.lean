import QECML.ClopperPearson

/-!
# The pre-registered acceptance arithmetic, checked by the kernel

Registered parameters: acceptance threshold `ε* = 5e-4`, per-type level `α = 2e-10`
(Bonferroni over five types: `5 α = 1e-9`).
* Design A (the registered design): `n = 1.2e5` samples per type, accept iff at most `k = 18` bad blocks.
* Design B (an alternative design, not used): `n = 8e4`, accept iff at most `k = 7` bad blocks.

For each design, the acceptance form `F(k; n, ε*) ≤ α` holds at the cutoff and fails one step above it. Since
`F(k; n, ·)` is antitone on `[0, 1]` (`binomCDF_antitoneOn`), `F(k; n, ε*) ≤ α` says exactly that the exact
one-sided Clopper–Pearson upper bound at level `α` is at most `ε*`.

All four are `decide +kernel` evaluations of closed Boolean checks plus the soundness lemmas; no `native_decide`.
-/

namespace QECML

/-- Design A: `F(18; 1.2e5, 5e-4) ≤ 2e-10`. -/
theorem cp_accept_A : binomCDF 120000 18 5e-4 ≤ 2e-10 := by
  have h := cpCheck_sound (n := 120000) (k := 18) (a := 1) (b := 2000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h ⊢
  exact h

/-- Design A, one step above the cutoff: `2e-10 < F(19; 1.2e5, 5e-4)`. -/
theorem cp_reject_A : 2e-10 < binomCDF 120000 19 5e-4 := by
  have h := cpCheckGt_sound (n := 120000) (k := 19) (a := 1) (b := 2000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h ⊢
  exact h

/-- Design B: `F(7; 8e4, 5e-4) ≤ 2e-10`. -/
theorem cp_accept_B : binomCDF 80000 7 5e-4 ≤ 2e-10 := by
  have h := cpCheck_sound (n := 80000) (k := 7) (a := 1) (b := 2000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h ⊢
  exact h

/-- Design B, one step above the cutoff: `2e-10 < F(8; 8e4, 5e-4)`. -/
theorem cp_reject_B : 2e-10 < binomCDF 80000 8 5e-4 := by
  have h := cpCheckGt_sound (n := 80000) (k := 8) (a := 1) (b := 2000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at h ⊢
  exact h

end QECML
