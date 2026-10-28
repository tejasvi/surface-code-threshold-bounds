import QECML.MonoQ
import QECML.MonoSize

/-!
# Theorem B from Theorem A

The proof steps of Theorem B:
* `P_ML,q ≤ P_ML,q*` for `q ≤ q* ≤ 1/2` (monotonicity in `q`, `pMLPlanar_mono_q`);
* `P_ML,q*(W, H) ≤ P_ML,q*(n_x L, n_y L)` with `n_x = max(5, ⌈W/L⌉)`, `n_y = ⌊H/L⌋` (monotonicity in the
  size, `pMLPlanar_mono_size`);
* `≤ Pr_{q*}(S3' fails)` on the `(n_x L, n_y L)` code (ML optimality, `pML_le_pFailCorr`);
* `≤` the bound (Theorem A, here the named hypothesis `TheoremA`).

The bound constants are a parameter (`BoundConsts`); `constsV11` holds the constants of an earlier parameter choice
(`ε* = 5e-4`, `a1 = 20`). In `QECML.S3.Hypotheses` the hypothesis `TheoremA` is derived from the 2D-lemma
hypothesis, the type-equality hypothesis and the statistical hypothesis.
-/

namespace QECML

/-- Constants of a bound `C1 n_x e^{-s1 (n_y - H0)} + C2 n_x e^{-s2 (n_y - H0)}`, stated for `n_y ≥ nyMin`. -/
structure BoundConsts where
  C1 : ℝ
  s1 : ℝ
  C2 : ℝ
  s2 : ℝ
  H0 : ℝ
  nyMin : ℕ

/-- The value of the bound at `(n_x, n_y)`. -/
noncomputable def BoundConsts.eval (K : BoundConsts) (nx ny : ℕ) : ℝ :=
  K.C1 * nx * Real.exp (-K.s1 * ((ny : ℝ) - K.H0)) + K.C2 * nx * Real.exp (-K.s2 * ((ny : ℝ) - K.H0))

/-- An earlier parameter choice (`ε* = 5e-4`, `a1 = 20`): `7.06e2 n_x e^{-0.1167 (n_y - 47)} + 4.45e6 n_x
e^{-0.0257 (n_y - 47)}` for `n_y ≥ 48`. -/
noncomputable def constsV11 : BoundConsts := ⟨7.06e2, 0.1167, 4.45e6, 0.0257, 47, 48⟩

/-- A decoder family with block side `L`: for the code with `W = n_x L` columns and `H = n_y L` rows, a map from
syndromes to corrections. -/
abbrev DecoderFamily (L : ℕ) : Type :=
  ∀ nx ny : ℕ, (PVert (nx * L - 1) (ny * L - 1) → ZMod 2) → (PEdge (nx * L - 1) (ny * L - 1) → ZMod 2)

/-- Theorem A as a named hypothesis: at rate `qstar`, the decoder family fails with probability at most the bound,
for `n_x ≥ 5` and `n_y ≥ nyMin`. -/
def TheoremA (K : BoundConsts) (qstar : ℝ) (L : ℕ) (dec : DecoderFamily L) : Prop :=
  ∀ nx ny : ℕ, 5 ≤ nx → K.nyMin ≤ ny →
    pFailCorr (bernProd qstar) (psyn (nx * L - 1) (ny * L - 1)) (pcls (nx * L - 1) (ny * L - 1)) (dec nx ny) ≤
      K.eval nx ny

/-- Block columns used by Theorem B: `n_x = max(5, ⌈W/L⌉)`. -/
def nxOf (L W : ℕ) : ℕ := max 5 ((W + L - 1) / L)

/-- Block rows used by Theorem B: `n_y = ⌊H/L⌋`. -/
def nyOf (L H : ℕ) : ℕ := H / L

theorem le_nxOf_mul {L W : ℕ} (hL : 1 ≤ L) : W ≤ nxOf L W * L := by
  have h1 : W + L - 1 < (W + L - 1) / L * L + L := Nat.lt_div_mul_add (by omega)
  have h2 : (W + L - 1) / L * L ≤ nxOf L W * L := Nat.mul_le_mul_right L (le_max_right _ _)
  omega

/-- **Theorem B from Theorem A** (any constants). For `q ≤ q* ≤ 1/2`, `W ≥ 1` and `H ≥ nyMin L`, the ML failure
probability of the planar code with `W` columns and `H` rows at rate `q` is at most the bound at
`(n_x, n_y) = (max(5, ⌈W/L⌉), ⌊H/L⌋)`. -/
theorem theoremB_of_theoremA (K : BoundConsts) {qstar : ℝ} (hqs0 : 0 ≤ qstar) (hqs : qstar ≤ 1 / 2) {L : ℕ}
    (hL : 1 ≤ L) (dec : DecoderFamily L) (hA : TheoremA K qstar L dec) {q : ℝ} (hq : q ≤ qstar) {W H : ℕ}
    (hW : 1 ≤ W) (hH : K.nyMin * L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤ K.eval (nxOf L W) (nyOf L H) := by
  set nx := nxOf L W
  set ny := nyOf L H
  have hnx5 : 5 ≤ nx := le_max_left _ _
  have hWnx : W ≤ nx * L := le_nxOf_mul hL
  have hnyH : ny * L ≤ H := Nat.div_mul_le_self H L
  have hny : K.nyMin ≤ ny := (Nat.le_div_iff_mul_le (by omega)).2 hH
  calc pMLPlanar (W - 1) (H - 1) q
      ≤ pMLPlanar (W - 1) (H - 1) qstar := pMLPlanar_mono_q _ _ hq hqs
    _ ≤ pMLPlanar (nx * L - 1) (ny * L - 1) qstar :=
        pMLPlanar_mono_size (by omega) (by omega) hqs0 (by linarith)
    _ ≤ pFailCorr (bernProd qstar) (psyn (nx * L - 1) (ny * L - 1)) (pcls (nx * L - 1) (ny * L - 1))
          (dec nx ny) :=
        pML_le_pFailCorr _ _ (pcls _ _) (bernProd_nonneg hqs0 (by linarith)) _
    _ ≤ K.eval nx ny := hA nx ny hnx5 hny

/-- **Theorem B (constants `constsV11`)**, conditional on Theorem A for the decoder family `dec` at `q* = 0.100`:
for every `q ≤ 0.100`, every `W ≥ 1` and every `H ≥ 48 L`,
`P_ML,q(fail) ≤ 7.06e2 n_x e^{-0.1167 (n_y - 47)} + 4.45e6 n_x e^{-0.0257 (n_y - 47)}`
with `n_x = max(5, ⌈W/L⌉)` and `n_y = ⌊H/L⌋`. -/
theorem theoremB_v1_1 {L : ℕ} (hL : 1 ≤ L) (dec : DecoderFamily L) (hA : TheoremA constsV11 0.100 L dec)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 48 * L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      7.06e2 * (nxOf L W : ℝ) * Real.exp (-0.1167 * ((nyOf L H : ℝ) - 47)) +
        4.45e6 * (nxOf L W : ℝ) * Real.exp (-0.0257 * ((nyOf L H : ℝ) - 47)) :=
  theoremB_of_theoremA constsV11 (by norm_num) (by norm_num) hL dec hA hq hW hH

end QECML
