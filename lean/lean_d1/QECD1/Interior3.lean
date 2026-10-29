import QECD1.Model3

/-!
# Lemma A on the 3D code, and the local handshake (core of interior parity)

* `Fadj X`: checks joined by an edge of the edge set `X` (`F = E + C0`). `Fadj_unit`: these are unit steps
  (`ends_adjacent`).
* `confine_model`: Lemma A (first part) on the 3D code. Suppose block `c` is not long: no `F`-walk inside
  `{distVB · c < 35}` from the check `x0 ∈ c` reaches distance 35. Then every check `F`-reachable from `x0` is within
  34 of `c`, and lies in a block of `N_1(c)`.
* `local_handshake`: let `U` be a set of checks closed under `F`-adjacency, with no half-edge of `F` touching it.
  Then the syndrome of `F` summed over `U` is 0. This is the 2D `psyn_restrictQ` plus `sum_psyn_eq_zero`, the core
  of `interior_parity` (P1):
  * the union of the `F`-components meeting an interior cluster reaches no rough side, so no half-edge of `F`
    touches it (`declared_of_rough`, A3);
  * its odd checks are the residual defects of the cluster (A2).
-/

namespace QECD1

variable {T w h : ℕ}

/-- Checks joined by an edge of `X`. -/
def Fadj (X : PEdge3 T w h → ZMod 2) (u v : PVert3 T w h) : Prop := ∃ e, X e = 1 ∧ u ∈ e.ends ∧ v ∈ e.ends

theorem Fadj_unit (X : PEdge3 T w h → ZMod 2) {u v : PVert3 T w h} (huv : Fadj X u v) :
    linf (u.toV3 - v.toV3) ≤ 1 := by
  obtain ⟨e, _, hu, hv⟩ := huv
  exact ends_adjacent e hu hv

/-- **Lemma A (first part) on the 3D code.** -/
theorem confine_model (X : PEdge3 T w h → ZMod 2) (c : V3) (x0 : PVert3 T w h) (hx0 : distVB x0.toV3 c = 0)
    (hnl : ∀ y, Relation.ReflTransGen (fun u v => Fadj X u v ∧ distVB u.toV3 c < 35) x0 y →
      distVB y.toV3 c ≠ 35) :
    ∀ y, Relation.ReflTransGen (Fadj X) x0 y → distVB y.toV3 c ≤ 34 ∧ dist3 (blockOf3 y) c ≤ 1 := by
  intro y hy
  have hd : ∀ u v, Fadj X u v → distVB v.toV3 c ≤ distVB u.toV3 c + 1 := fun u v huv =>
    distVB_lip u.toV3 v.toV3 c (Fadj_unit X huv)
  have h := first_exit (Fadj X) (fun p => distVB p.toV3 c) hd 35 (by norm_num) x0 hx0 hnl y hy
  exact ⟨h.1, blockOf_near y.toV3 c (by have := h.1; omega)⟩

/-- The restriction of `X` to the edges with an end in `U`. -/
noncomputable def restrictE (X : PEdge3 T w h → ZMod 2) (U : Finset (PVert3 T w h)) (e : PEdge3 T w h) : ZMod 2 :=
  if ∃ v ∈ U, v ∈ e.ends then X e else 0

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- **Local handshake.** -/
theorem local_handshake (X : PEdge3 T w h → ZMod 2) (U : Finset (PVert3 T w h))
    (hU : ∀ u ∈ U, ∀ v, Fadj X u v → v ∈ U)
    (hrough : ∀ e, e.isHalf → X e = 1 → ∀ v ∈ e.ends, v ∉ U) :
    ∑ v ∈ U, psyn3 X v = 0 := by
  classical
  set rX := restrictE X U
  -- on `U` the restriction has the same syndrome
  have h1 : ∀ v ∈ U, psyn3 X v = psyn3 rX v := by
    intro v hv
    simp only [psyn3]
    refine Finset.sum_congr rfl fun e he => ?_
    have hve := (Finset.mem_filter.1 he).2
    simp only [rX, restrictE]
    rw [if_pos ⟨v, hv, hve⟩]
  -- off `U` the restriction has no syndrome
  have h2 : ∀ v, v ∉ U → psyn3 rX v = 0 := by
    intro v hv
    simp only [psyn3]
    refine Finset.sum_eq_zero fun e he => ?_
    have hve := (Finset.mem_filter.1 he).2
    simp only [rX, restrictE]
    split_ifs with hex
    · obtain ⟨u, hu, hue⟩ := hex
      rcases zmod2_cases (X e) with h0 | h0
      · exact h0
      · exact absurd (hU u hu v ⟨e, h0, hue, hve⟩) hv
    · rfl
  -- no half-edge of the restriction is chosen
  have h3 : ∀ e, e.isHalf → rX e = 0 := by
    intro e he
    simp only [rX, restrictE]
    split_ifs with hex
    · obtain ⟨u, hu, hue⟩ := hex
      rcases zmod2_cases (X e) with h0 | h0
      · exact h0
      · exact absurd hu (hrough e he h0 u hue)
    · rfl
  calc ∑ v ∈ U, psyn3 X v = ∑ v ∈ U, psyn3 rX v := Finset.sum_congr rfl h1
    _ = ∑ v, psyn3 rX v := by
        rw [← Finset.sum_subset (Finset.subset_univ U) (fun v _ hv => h2 v hv)]
    _ = 0 := sum_psyn3_eq_zero rX h3

end QECD1
