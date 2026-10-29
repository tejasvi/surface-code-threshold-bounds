import QECD1.Keys

/-!
# The refined 3D T2 count: the family bound `FamB3` and the transfer ratio, from a named encoding hypothesis

`Encoding3D` is the named hypothesis that the 3D deterministic lemma must discharge.
The type `FK` stands for the 3D family keys from a landing root, and `w` for their T2 weights.
Each key gets:

* an axis `ax k`, along which its witness spans at least `Sw = 17` (by `span_indicator_le` some axis does);
* an encoding `enc k`, a key of that axis that is valid (`KeyOK`). Validity means:
  * the route grammar, with steps in `S0 = {D ≤ |v|∞ ≤ A0}`, links in `S1 = {D ≤ |v|∞ ≤ A1}`, the leaf
    convention, and the witness condition `|z| ≥ Sw` (all walks at `Asp`);
  * all of it with the exact constants of `QECD1.Params`;
  * this is possible because the roots are actual odd blocks, `RootsActual`; see `QECD1.Rooting`;
* injectivity per axis, and a weight that `keyWt` dominates.

From it:

* `famB3`: every finite set of 3D family keys weighs at most `F0s = 2 F0t + F0y ≈ 8.210e-3`;
* `famB3_ratio_le`: with the tilted landing sum over `|v|∞ ≥ J = 17`, `e^{30 λ}` and `ε*`, the transfer ratio is at
  most 0.9 (`λ = 0.014`, `s = 0.007`).
-/

namespace QECD1

/-- **Named hypothesis**: the encoding of the 3D family keys `FK` (weights `w`) into the per-axis keys. -/
structure Encoding3D (FK : Type) where
  w : FK → ℝ
  ax : FK → Fin 3
  enc : FK → Key
  ok : ∀ k, KeyOK (ax k) (enc k)
  le : ∀ k, w k ≤ keyWt (ax k) (enc k)
  inj : ∀ k k', ax k = ax k' → enc k = enc k' → k = k'

/-- The certified bound of the axis-`j` keys. -/
noncomputable def F0ax (j : Fin 3) : ℝ := if j = 2 then (2741437430948 : ℝ) / 10 ^ 15 else (2734104547231 : ℝ) / 10 ^ 15

theorem keys_ax_le (j : Fin 3) (K : Finset Key) (hK : ∀ k ∈ K, KeyOK j k) : ∑ k ∈ K, keyWt j k ≤ F0ax j := by
  unfold F0ax
  fin_cases j
  · exact keysT_le K hK
  · exact keysX_le K hK
  · exact keysY_le K hK

/-- **`FamB3`**: every finite set of 3D family keys weighs at most `F0s`. -/
theorem famB3 {FK : Type} (E : Encoding3D FK) (K : Finset FK) : ∑ k ∈ K, E.w k ≤ F0s := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := E.ax) (t := Finset.univ) (fun k _ => Finset.mem_univ _)]
  have hj : ∀ j : Fin 3, ∑ k ∈ K with E.ax k = j, E.w k ≤ F0ax j := by
    intro j
    set Kj := K.filter fun k => E.ax k = j
    have h1 : ∑ k ∈ Kj, E.w k ≤ ∑ k ∈ Kj, keyWt j (E.enc k) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hax : E.ax k = j := (Finset.mem_filter.1 hk).2
      have := E.le k
      rw [hax] at this
      exact this
    have hinj : Set.InjOn E.enc (Kj : Set FK) := by
      intro k hk k' hk' h
      have a : E.ax k = j := (Finset.mem_filter.1 hk).2
      have b : E.ax k' = j := (Finset.mem_filter.1 hk').2
      exact E.inj k k' (a.trans b.symm) h
    have h2 : ∑ k ∈ Kj, keyWt j (E.enc k) = ∑ key ∈ Kj.image E.enc, keyWt j key := (Finset.sum_image hinj).symm
    have h3 : ∑ key ∈ Kj.image E.enc, keyWt j key ≤ F0ax j := by
      refine keys_ax_le j _ fun key hkey => ?_
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hkey
      have hax : E.ax k = j := (Finset.mem_filter.1 hk).2
      have := E.ok k
      rw [hax] at this
      exact this
    linarith
  calc ∑ j : Fin 3, ∑ k ∈ K with E.ax k = j, E.w k ≤ ∑ j : Fin 3, F0ax j := Finset.sum_le_sum fun j _ => hj j
    _ = F0s := by
      rw [Fin.sum_univ_three]
      unfold F0ax F0s
      norm_num

/-- **The transfer ratio of the refined 3D T2 count is at most 0.9**, given the encoding hypothesis. -/
theorem famB3_ratio_le {FK : Type} (E : Encoding3D FK) (K : Finset FK) (hw : ∀ k, 0 ≤ E.w k)
    (S : Finset V3) (hS : ∀ v ∈ S, Const.J ≤ linf v) :
    (∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2)) * Real.exp (lam * 30) * eps * (∑ k ∈ K, E.w k) ≤ 9 / 10 := by
  have hJ := landing_tilt_le S fun v hv => by
    have h := hS v hv
    rw [Const.J_val] at h
    exact h
  have hE : Real.exp (lam * 30) ≤ (eoffUpT : ℝ) := by
    exact exp_offT_le
  have hK := famB3 E K
  have hK0 : 0 ≤ ∑ k ∈ K, E.w k := Finset.sum_nonneg fun k _ => hw k
  have hs0 : 0 ≤ ∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have he0 : (0 : ℝ) ≤ eps := eps_nonneg
  have hm1 : (∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2)) * Real.exp (lam * 30) ≤ Jbar2 * (eoffUpT : ℝ) :=
    mul_le_mul hJ hE (Real.exp_pos _).le (le_trans hs0 hJ)
  have hJ0 : 0 ≤ Jbar2 * (eoffUpT : ℝ) := le_trans (mul_nonneg hs0 (Real.exp_pos _).le) hm1
  have hm2 := mul_le_mul_of_nonneg_right hm1 he0
  have hm3 := mul_le_mul hm2 hK hK0 (mul_nonneg hJ0 he0)
  have h4 : Jbar2 * (eoffUpT : ℝ) * eps * F0s ≤ 9 / 10 := by
    have e : eps = 37 / 2000000 := rfl
    rw [e]
    exact ratio_s_num
  linarith

end QECD1
