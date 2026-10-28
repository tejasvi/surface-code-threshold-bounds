import QECML.TwoD.T2Fac
import QECML.TwoD.T2Auto

/-!
# The family factor and the excursion factor of the T2 count (automata at the parameters of the T2 summation)

Route words of a cluster route, read from a root: steps along the route part, a leaf when the part is empty, links
to the next root. `St4` refines the grammar state by the steps of the current part (`B` at a root, `A1` after one
step, `A2` after two or more, `C` after a leaf), so that a word can be required to end with a part of two or more
steps (the excursion of an off-route witness, whose last part spans at least `a1 + 2 - D > A0`).

* `exAut ε`: excursion words, every move weighted `ε` (untilted), ending only in `A2`. Bellman values
  `(B, A1, A2, C) = (0.0136, 0.1238, 1.1238, 0.00686)` at `ε = 5e-4` (`exAut_le`).
* `famAut`: family words with one witness mark (the unit token, which does not move the route), moves weighted by
  the T2 weights `t2g` (tilted), the mark in state `x` weighted `mk x` (the witness: on-route walks of at least
  `2, 1, 0, 1` steps from a root, a first step, a later step, a leaf, or an off-route walk with an excursion),
  ending after the mark in `A1`, `A2` or `C`. Bellman values: before the mark `(0.1935, 0.876, 2.676, 0.4055)`,
  after it `(0.449, 1.8, 1.8, 1.508)` (`famAut_le`). The family factor is `ε · 0.1935` (the landing root's `ε`).
-/

open Finset Classical

namespace QECML

namespace S3Geom

/-- Grammar states with the step count of the current part. -/
inductive St4 where
  | B
  | A1
  | A2
  | C
  deriving DecidableEq

variable {G : S3Geom}

/-- The moves allowed in a state (`S0` steps and leaves, `S1` links). -/
def St4.allowed (D A0 A1 : ℕ) : St4 → G.Block → G.Move → Prop
  | .B, cur, .step b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0
  | .B, cur, .leaf b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0
  | .A1, cur, .step b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0
  | .A1, cur, .link b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1
  | .A2, cur, .step b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0
  | .A2, cur, .link b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1
  | .C, cur, .link b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1
  | _, _, _ => False

/-- The state after a move. -/
def St4.next : St4 → G.Move → St4
  | .B, .step _ => .A1
  | _, .step _ => .A2
  | _, .leaf _ => .C
  | _, .link _ => .B

/-! ### One-move sums in each state -/

section Moves

variable {D A0 A1 : ℕ} {gm : G.Block → G.Move → ℝ} {u0 u1 l0 : ℝ} (hg : ∀ cur m, 0 ≤ gm cur m)
  (hu0 : ∀ cur : G.Block, ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0),
    gm cur (.step b) ≤ u0)
  (hu1 : ∀ cur : G.Block, ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1),
    gm cur (.link b) ≤ u1)
  (hl0 : ∀ cur : G.Block, ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0),
    gm cur (.leaf b) ≤ l0)

include hg hu0 hu1 hl0

/-- The one-move sum in a state, against values `f` of the next state. -/
theorem st4_moves_le (f : St4 → ℝ) (hf : ∀ x, 0 ≤ f x) (x : St4) (cur : G.Block) :
    ∑ m : G.Move, (if St4.allowed D A0 A1 x cur m then gm cur m * f (St4.next x m) else 0) ≤
      match x with
      | .B => u0 * f .A1 + l0 * f .C
      | .A1 => u0 * f .A2 + u1 * f .B
      | .A2 => u0 * f .A2 + u1 * f .B
      | .C => u1 * f .B := by
  rw [sum_move]
  have hS : ∀ (P : G.Block → Prop) [DecidablePred P] (Q : G.Block → Prop) (_hQ : DecidablePred Q)
      (hQP : ∀ b, Q b → P b) (k : G.Block → G.Move) (v : ℝ) (hv : 0 ≤ v),
      ∑ b, (if Q b then gm cur (k b) * v else 0) ≤ v * ∑ b ∈ univ.filter P, gm cur (k b) := by
    intro P _ Q _ hQP k v hv
    exact sum_ite_bound P hQP (fun b => gm cur (k b)) (fun b => rfl) (fun b => hg cur _) hv (fun b _ => le_rfl)
  cases x with
  | B =>
    have h1 := hS (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0)
      (fun b => St4.allowed D A0 A1 .B cur (.step b)) (fun _ => Classical.propDecidable _) (fun b h => h) (fun b => .step b) (f .A1) (hf _)
    have h3 := hS (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0)
      (fun b => St4.allowed D A0 A1 .B cur (.leaf b)) (fun _ => Classical.propDecidable _) (fun b h => h) (fun b => .leaf b) (f .C) (hf _)
    have h2 : ∑ b : G.Block, (if St4.allowed D A0 A1 .B cur (.link b) then
        gm cur (.link b) * f (St4.next .B (.link b)) else 0) = 0 :=
      Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h)
    simp only [St4.next] at h1 h3 h2 ⊢
    rw [h2]
    have e1 := mul_le_mul_of_nonneg_left (hu0 cur) (hf .A1)
    have e3 := mul_le_mul_of_nonneg_left (hl0 cur) (hf .C)
    linarith
  | A1 =>
    have h1 := hS (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0)
      (fun b => St4.allowed D A0 A1 .A1 cur (.step b)) (fun _ => Classical.propDecidable _) (fun b h => h) (fun b => .step b) (f .A2) (hf _)
    have h2 := hS (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1)
      (fun b => St4.allowed D A0 A1 .A1 cur (.link b)) (fun _ => Classical.propDecidable _) (fun b h => h) (fun b => .link b) (f .B) (hf _)
    have h3 : ∑ b : G.Block, (if St4.allowed D A0 A1 .A1 cur (.leaf b) then
        gm cur (.leaf b) * f (St4.next .A1 (.leaf b)) else 0) = 0 :=
      Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h)
    simp only [St4.next] at h1 h2 h3 ⊢
    rw [h3]
    have e1 := mul_le_mul_of_nonneg_left (hu0 cur) (hf .A2)
    have e2 := mul_le_mul_of_nonneg_left (hu1 cur) (hf .B)
    linarith
  | A2 =>
    have h1 := hS (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0)
      (fun b => St4.allowed D A0 A1 .A2 cur (.step b)) (fun _ => Classical.propDecidable _) (fun b h => h) (fun b => .step b) (f .A2) (hf _)
    have h2 := hS (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1)
      (fun b => St4.allowed D A0 A1 .A2 cur (.link b)) (fun _ => Classical.propDecidable _) (fun b h => h) (fun b => .link b) (f .B) (hf _)
    have h3 : ∑ b : G.Block, (if St4.allowed D A0 A1 .A2 cur (.leaf b) then
        gm cur (.leaf b) * f (St4.next .A2 (.leaf b)) else 0) = 0 :=
      Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h)
    simp only [St4.next] at h1 h2 h3 ⊢
    rw [h3]
    have e1 := mul_le_mul_of_nonneg_left (hu0 cur) (hf .A2)
    have e2 := mul_le_mul_of_nonneg_left (hu1 cur) (hf .B)
    linarith
  | C =>
    have h2 := hS (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1)
      (fun b => St4.allowed D A0 A1 .C cur (.link b)) (fun _ => Classical.propDecidable _) (fun b h => h) (fun b => .link b) (f .B) (hf _)
    have h1 : ∑ b : G.Block, (if St4.allowed D A0 A1 .C cur (.step b) then
        gm cur (.step b) * f (St4.next .C (.step b)) else 0) = 0 :=
      Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h)
    have h3 : ∑ b : G.Block, (if St4.allowed D A0 A1 .C cur (.leaf b) then
        gm cur (.leaf b) * f (St4.next .C (.leaf b)) else 0) = 0 :=
      Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h)
    simp only [St4.next] at h1 h2 h3 ⊢
    rw [h1, h3]
    have e2 := mul_le_mul_of_nonneg_left (hu1 cur) (hf .B)
    linarith

end Moves

/-! ### The excursion automaton -/

/-- Excursion words: every move weighted `ε` (untilted); words end only in `A2` (a last part of two or more
steps). -/
noncomputable def exAut (D A0 A1 : ℕ) (ε : ℝ) : WAut G St4 G.Move where
  allowed := St4.allowed D A0 A1
  nq := St4.next
  nb := nextBlk
  g := fun _ _ _ => ε
  e := fun q => if q = .A2 then 1 else 0

/-- Bellman values of the excursion automaton. -/
def exVal : St4 → ℝ
  | .B => 0.0136
  | .A1 => 0.1238
  | .A2 => 1.1238
  | .C => 0.00686

theorem card_S0_le (hD : G.D = 5) (cur : G.Block) :
    ∑ _b ∈ univ.filter (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + 4), (5e-4 : ℝ) ≤
      5e-4 * 208 := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have h1 := card_offsets_le (G := G) G.D (G.D - 1 + 4) cur
  have hcard : Tbox 5 8 0 = 208 := by
    simp only [Tbox, zero_mul, Real.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one, card_offBox_5_8]
    norm_num
  rw [hD] at h1 ⊢
  exact h1.trans (le_of_eq hcard)

theorem card_S1_le (hD : G.D = 5) (cur : G.Block) :
    ∑ _b ∈ univ.filter (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + 12), (5e-4 : ℝ) ≤
      5e-4 * 1008 := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have h1 := card_offsets_le (G := G) G.D (G.D - 1 + 12) cur
  have hcard : Tbox 5 16 0 = 1008 := by
    simp only [Tbox, zero_mul, Real.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one, card_offBox_5_16]
    norm_num
  rw [hD] at h1 ⊢
  exact h1.trans (le_of_eq hcard)

/-- **The excursion factor**: excursion words from any block and state weigh at most `exVal`. -/
theorem exAut_le (hD : G.D = 5) (N : ℕ) (q : St4) (cur : G.Block) :
    (exAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) 5e-4).V N q cur ≤ exVal q := by
  refine WAut.V_le _ (fun _ _ _ => by norm_num [exAut]) exVal (fun q cur => ?_) (fun q => by cases q <;> norm_num [exVal]) N q cur
  have hm := st4_moves_le (gm := fun _ _ => (5e-4 : ℝ)) (fun _ _ => by norm_num)
    (fun cur => card_S0_le hD cur) (fun cur => card_S1_le hD cur) (fun cur => card_S0_le hD cur) exVal
    (fun q => by cases q <;> norm_num [exVal]) q cur
  show (if q = .A2 then (1 : ℝ) else 0) +
    ∑ t : G.Move, (if St4.allowed G.D (G.D - 1 + 4) (G.D - 1 + 12) q cur t then (5e-4 : ℝ) * exVal (St4.next q t)
      else 0) ≤ exVal q
  cases q with
  | B =>
    simp only [reduceCtorEq, ↓reduceIte, zero_add] at hm ⊢
    refine hm.trans ?_
    norm_num [exVal]
  | A1 =>
    simp only [reduceCtorEq, ↓reduceIte, zero_add] at hm ⊢
    refine hm.trans ?_
    norm_num [exVal]
  | A2 =>
    simp only [↓reduceIte] at hm ⊢
    have e2 : exVal St4.A2 = 1.1238 := rfl
    have e1 : exVal St4.B = 0.0136 := rfl
    rw [e2, e1] at hm
    rw [e2]
    linarith
  | C =>
    simp only [reduceCtorEq, ↓reduceIte, zero_add] at hm ⊢
    refine hm.trans ?_
    norm_num [exVal]

/-! ### The family automaton -/

/-- The mark weights (witness factors), with `y = ε T0`, `z = ε T1` and the excursion value `0.0136`: on-route walks
of at least `2` (`B`), `1` (`A1`, `C`), `0` (`A2`) steps, `Σ_{c ≥ c_min} y^c`, plus an off-route walk of any length
`1 / (1 - y)` times a link `z` times the excursion value. -/
noncomputable def mkW : St4 → ℝ
  | .B => ((5e-4 * 208) ^ 2 + 5e-4 * 1008 * 0.0136) / (1 - 5e-4 * 208)
  | .A1 => (5e-4 * 208 + 5e-4 * 1008 * 0.0136) / (1 - 5e-4 * 208)
  | .A2 => (1 + 5e-4 * 1008 * 0.0136) / (1 - 5e-4 * 208)
  | .C => (5e-4 * 208 + 5e-4 * 1008 * 0.0136) / (1 - 5e-4 * 208)

/-- Family words with one witness mark (`false` before the mark, `true` after it). -/
noncomputable def famAut (D A0 A1 : ℕ) : WAut G (St4 × Bool) (G.Move ⊕ Unit) where
  allowed := fun q cur t => match q, t with
    | (x, _), .inl m => St4.allowed D A0 A1 x cur m
    | (_, false), .inr _ => True
    | (_, true), .inr _ => False
  nq := fun q t => match q, t with
    | (x, p), .inl m => (St4.next x m, p)
    | (x, _), .inr _ => (x, true)
  nb := fun cur t => match t with
    | .inl m => nextBlk cur m
    | .inr _ => cur
  g := fun q cur t => match q, t with
    | _, .inl m => t2g 5e-4 0.04305 0.02 cur m
    | (x, _), .inr _ => mkW x
  e := fun q => match q with
    | (.B, true) => 0
    | (_, true) => 1
    | (_, false) => 0

/-- Bellman values of the family automaton. -/
def famVal : St4 × Bool → ℝ
  | (.B, false) => 0.1935
  | (.A1, false) => 0.876
  | (.A2, false) => 2.676
  | (.C, false) => 0.4055
  | (.B, true) => 0.449
  | (.A1, true) => 1.8
  | (.A2, true) => 1.8
  | (.C, true) => 1.508

theorem famVal_nonneg (q : St4 × Bool) : 0 ≤ famVal q := by
  obtain ⟨x, p⟩ := q
  cases x <;> cases p <;> norm_num [famVal]

theorem mkW_nonneg (x : St4) : 0 ≤ mkW x := by
  cases x <;> norm_num [mkW]

/-- **The family factor**: family words from any block and state weigh at most `famVal`. -/
theorem famAut_le (hD : G.D = 5) (N : ℕ) (q : St4 × Bool) (cur : G.Block) :
    (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).V N q cur ≤ famVal q := by
  refine WAut.V_le _ (fun q cur t => ?_) famVal (fun q cur => ?_) famVal_nonneg N q cur
  · obtain ⟨x, p⟩ := q
    rcases t with m | u
    · exact t2g_nonneg (by norm_num) _ _ _ _
    · exact mkW_nonneg x
  · obtain ⟨x, p⟩ := q
    rw [Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)]
    have hm := st4_moves_le (gm := t2g 5e-4 0.04305 0.02) (t2g_nonneg (by norm_num) _ _)
      (fun cur => t2_u0 cur hD) (fun cur => t2_u1 cur hD) (fun cur => t2_l0 cur hD) (fun y => famVal (y, p))
      (fun y => famVal_nonneg _) x cur
    have hinl : (∑ m : G.Move, if (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).allowed (x, p) cur (Sum.inl m)
        then (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).g (x, p) cur (Sum.inl m) *
          famVal ((famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).nq (x, p) (Sum.inl m)) else 0) =
        ∑ m : G.Move, if St4.allowed G.D (G.D - 1 + 4) (G.D - 1 + 12) x cur m then
          t2g 5e-4 0.04305 0.02 cur m * famVal (St4.next x m, p) else 0 := rfl
    rw [hinl]
    cases p with
    | false =>
      have hinr : (if (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).allowed (x, false) cur
          (Sum.inr default) then (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).g (x, false) cur
            (Sum.inr default) * famVal ((famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).nq (x, false)
              (Sum.inr default)) else 0) = mkW x * famVal (x, true) :=
        ite_eq_left (show (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).allowed (x, false) cur
          (Sum.inr default) from trivial)
      have he : (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).e (x, false) = 0 := by
        cases x <;> rfl
      rw [hinr, he, zero_add]
      cases x <;> simp only at hm <;> norm_num [famVal, mkW] at hm ⊢ <;> linarith
    | true =>
      have hinr : (if (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).allowed (x, true) cur
          (Sum.inr default) then (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).g (x, true) cur
            (Sum.inr default) * famVal ((famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).nq (x, true)
              (Sum.inr default)) else 0) = 0 :=
        ite_eq_right (show ¬ (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).allowed (x, true) cur
          (Sum.inr default) from fun h => h)
      rw [hinr, add_zero]
      cases x with
      | B =>
        have he : (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).e (.B, true) = 0 := rfl
        rw [he, zero_add]
        simp only at hm
        norm_num [famVal] at hm ⊢
        linarith
      | A1 =>
        have he : (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).e (.A1, true) = 1 := rfl
        rw [he]
        simp only at hm
        norm_num [famVal] at hm ⊢
        linarith
      | A2 =>
        have he : (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).e (.A2, true) = 1 := rfl
        rw [he]
        simp only at hm
        norm_num [famVal] at hm ⊢
        linarith
      | C =>
        have he : (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).e (.C, true) = 1 := rfl
        rw [he]
        simp only at hm
        norm_num [famVal] at hm ⊢
        linarith

end S3Geom

end QECML
