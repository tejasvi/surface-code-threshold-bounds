import QECD1.LemmaA3

/-!
# Parity, witnesses, and interior clusters (the dimension-free core of Lemmas W0 and W1)

The 2D W0 and W1 (TwoD/Parity, TwoD/W1) find the parity witness. An odd component inside an interior cluster
(resp. an all-interior level-1 component) forces another odd component nearby. That component is more than `a0`
(resp. `a1`) blocks away, which gives the witness span. The counting core does not depend on the dimension:

* `handshake`: in any finite graph whose edges have one or two ends, the syndrome summed over all vertices equals
  the number of chosen one-ended edges (half-edges) mod 2. With no half-edges chosen, the number of odd vertices is
  even (2D `sum_psyn_eq_zero`).
* `parity_witness`: among finitely many components of total parity 0, an odd one has an odd partner.
* `witness_far`: the partner's flagged blocks are more than `a` blocks from the first component (`comp_sep`).
  With `a = a1` this is the hypothesis of `witness_span` (Sw = 17).
* `declared3`: in 3D only the y-rows `0, 1, n_y - 2, n_y - 1` are declared. The t and x sides are smooth: no
  half-edges, and the final round is perfect.
* `interior_rows`: a flagged block whose cluster contains no declared block lies in rows
  `2 + a0 ≤ y ≤ n_y - 3 - a0` (2D `rows_of_clusterUnion`). A closer declared row would join its cluster, since
  declared blocks are flagged by convention (i); only the declared blocks within `a0` of the block are used.
-/

namespace QECD1

open Finset

/-- **Handshake.** `ends e` is the set of ends of edge `e`; `X` is the set of chosen edges. -/
theorem handshake {V Ed : Type} [DecidableEq V] [DecidableEq Ed] (Vs : Finset V) (ends : Ed → Finset V)
    (X : Finset Ed) (hX : ∀ e ∈ X, ends e ⊆ Vs) :
    ∑ v ∈ Vs, ((X.filter fun e => v ∈ ends e).card : ZMod 2) = ∑ e ∈ X, ((ends e).card : ZMod 2) := by
  have h1 : ∀ v ∈ Vs, ((X.filter fun e => v ∈ ends e).card : ZMod 2) =
      ∑ e ∈ X, if v ∈ ends e then (1 : ZMod 2) else 0 := by
    intro v _
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hX e he)]

/-- **Handshake without half-edges**: if every chosen edge has two ends, the syndrome sums to zero. -/
theorem handshake_even {V Ed : Type} [DecidableEq V] [DecidableEq Ed] (Vs : Finset V) (ends : Ed → Finset V)
    (X : Finset Ed) (hX : ∀ e ∈ X, ends e ⊆ Vs) (h2 : ∀ e ∈ X, (ends e).card = 2) :
    ∑ v ∈ Vs, ((X.filter fun e => v ∈ ends e).card : ZMod 2) = 0 := by
  rw [handshake Vs ends X hX]
  refine Finset.sum_eq_zero fun e he => ?_
  rw [h2 e he]
  rfl

/-- **Parity witness**: among components of total parity 0, an odd component has an odd partner. -/
theorem parity_witness {ι : Type} [DecidableEq ι] (comps : Finset ι) (par : ι → ZMod 2)
    (htot : ∑ c ∈ comps, par c = 0) {C : ι} (hC : C ∈ comps) (hodd : par C = 1) :
    ∃ C' ∈ comps, C' ≠ C ∧ par C' = 1 := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have h0 : ∀ c ∈ comps.erase C, par c = 0 := by
    intro c hc
    have hne := Finset.ne_of_mem_erase hc
    have hmem := Finset.mem_of_mem_erase hc
    have hpar : par c ≠ 1 := hno c hmem hne
    generalize par c = x at hpar ⊢
    revert x
    decide
  rw [← Finset.add_sum_erase comps par hC, hodd, Finset.sum_eq_zero h0] at htot
  exact absurd htot (by decide)

/-- **The witness is far**: flagged blocks of different `a`-components are more than `a` apart. -/
theorem witness_far (F : Finset V3) (a : ℕ) {x w : V3} (hx : x ∈ F) (hw : w ∈ F) (hdiff : ¬ SameComp F a x w) :
    a + 1 ≤ dist3 x w :=
  comp_sep F a hx hw hdiff

/-- Declared blocks in 3D: the y-rows `0, 1, n_y - 2, n_y - 1` only. -/
def declared3 (ny : ℕ) (c : V3) : Prop := c.2.2 < 2 ∨ (ny : ℤ) ≤ c.2.2 + 2

/-- **Interior clusters keep away from the declared rows.** Suppose the declared blocks within `a0` of the flagged
block `c` are flagged (convention (i), needed only there), and the `a0`-cluster of `c` contains no declared block.
Then `c` lies in rows `2 + a0 ≤ y ≤ n_y - 3 - a0`. -/
theorem interior_rows (F : Finset V3) (ny : ℕ) {c : V3} (hc : c ∈ F)
    (hdecl : ∀ d : V3, declared3 ny d → dist3 c d ≤ Const.a0 → d ∈ F)
    (hint : ∀ d, SameComp F Const.a0 c d → ¬ declared3 ny d) :
    2 + (Const.a0 : ℤ) ≤ c.2.2 ∧ c.2.2 + 3 + Const.a0 ≤ (ny : ℤ) := by
  have hnd := hint c .refl
  simp only [declared3, not_or, not_lt] at hnd
  have ha : ((Const.a0 : ℕ) : ℤ) = 4 := by norm_num [Const.a0]
  rw [ha]
  constructor
  · by_contra hlt
    let d : V3 := (c.1, c.2.1, 1)
    have hd : declared3 ny d := Or.inl (by simp [d])
    have hdist : dist3 c d ≤ Const.a0 := by
      simp only [dist3, linf, Prod.fst_sub, Prod.snd_sub, d, Const.a0, sub_self, Int.natAbs_zero,
        max_le_iff]
      omega
    exact hint d (Relation.ReflTransGen.single ⟨hc, hdecl d hd hdist, hdist⟩) hd
  · by_contra hlt
    let d : V3 := (c.1, c.2.1, (ny : ℤ) - 2)
    have hd : declared3 ny d := Or.inr (by simp [d])
    have hdist : dist3 c d ≤ Const.a0 := by
      simp only [dist3, linf, Prod.fst_sub, Prod.snd_sub, d, Const.a0, sub_self, Int.natAbs_zero,
        max_le_iff]
      omega
    exact hint d (Relation.ReflTransGen.single ⟨hc, hdecl d hd hdist, hdist⟩) hd

end QECD1
