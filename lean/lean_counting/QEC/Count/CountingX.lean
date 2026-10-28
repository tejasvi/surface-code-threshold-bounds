import QEC.Count.Counting

/-!
# Counting with memory for any exclusion predicate

`Legal`, `Succ` and `sum_legal_le` (`Counting.lean`) with the exclusion predicate `Excl n c` replaced by any predicate
`X` on labelled windows (used with the SAFE exclusions `ExclS`). The proof is that of `sum_legal_le`.
-/

namespace QEC

open Finset QECComp

variable (n : ℕ) (X : List (ℕ × Bool) → Prop)

/-- Legal labelled walks for windows of up to `M` edges and the exclusion predicate `X`. -/
def LegalX (M : ℕ) (w : List (ℕ × Bool)) : Prop :=
  SelfAv n w ∧ DirOK n w ∧ ∀ i m, 2 ≤ m → m ≤ M → i + m ≤ w.length → ¬ X ((w.drop i).take m)

/-- Legal successors for the exclusion predicate `X`. -/
def SuccX (s : List (ℕ × Bool)) (x : ℕ × Bool) : Prop :=
  x.1 < 2 * n ∧ SelfAv n (s ++ [x]) ∧
    ∀ m, 2 ≤ m → m ≤ s.length + 1 → ¬ X ((s ++ [x]).drop (s.length + 1 - m))

namespace CountingX

variable {n : ℕ} {X : List (ℕ × Bool) → Prop}

theorem legalX_take {M : ℕ} {w : List (ℕ × Bool)} (h : LegalX n X M w) (k : ℕ) : LegalX n X M (w.take k) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Counting.selfAv_take h1 k, fun x hx => h2 x (List.mem_of_mem_take hx), ?_⟩
  intro i m hm2 hmM him
  have hlen : (w.take k).length = min k w.length := List.length_take
  have heq : ((w.take k).drop i).take m = (w.drop i).take m := by
    rw [List.drop_take, List.take_take]
    congr 1
    omega
  rw [heq]
  exact h3 i m hm2 hmM (by omega)

theorem legalX_tail {M : ℕ} {w : List (ℕ × Bool)} (h : LegalX n X M w) : LegalX n X M w.tail := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Counting.selfAv_tail h1, fun x hx => h2 x (List.mem_of_mem_tail hx), ?_⟩
  intro i m hm2 hmM him
  rw [List.drop_tail]
  rw [List.length_tail] at him
  exact h3 (i + 1) m hm2 hmM (by omega)

/-- A legal walk `s ++ x :: rest` with `|s| = K`: `x` is a legal successor of `s`. -/
theorem succX_of_legalX {K : ℕ} {s : List (ℕ × Bool)} {x : ℕ × Bool} {rest : List (ℕ × Bool)}
    (hs : s.length = K) (h : LegalX n X (K + 1) (s ++ x :: rest)) : SuccX n X s x := by
  have htake : (s ++ x :: rest).take (K + 1) = s ++ [x] := by
    rw [List.take_append, List.take_of_length_le (by omega), hs,
      show K + 1 - K = 1 by omega]
    rfl
  have hlegK := legalX_take h (K + 1)
  rw [htake] at hlegK
  refine ⟨h.2.1 x (by simp), hlegK.1, ?_⟩
  intro m hm2 hmM
  rw [hs] at hmM ⊢
  have hwin : (s ++ [x]).drop (K + 1 - m) = ((s ++ [x]).drop (K + 1 - m)).take m := by
    rw [List.take_of_length_le]
    simp [hs]
    omega
  rw [hwin]
  exact hlegK.2.2 (K + 1 - m) m hm2 hmM (by simp [hs]; omega)

end CountingX

open Counting CountingX in
open scoped Classical in
/-- **Counting with memory**, any exclusion predicate. -/
theorem sum_legal_leX (K : ℕ) {ωE ωC lam Hmin : ℝ} (hE : 0 ≤ ωE) (hC : 0 ≤ ωC)
    (hlam : 0 ≤ lam) (hHmin : 0 < Hmin) (IsSt : List (ℕ × Bool) → Prop) (H : List (ℕ × Bool) → ℝ)
    (hlen : ∀ s, IsSt s → s.length = K ∧ DirOK n s)
    (hpos : ∀ s, IsSt s → Hmin ≤ H s)
    (hstart : ∀ s, s.length = K → LegalX n X (K + 1) s → IsSt s)
    (hclosed : ∀ s, IsSt s → ∀ x, SuccX n X s x → IsSt (s ++ [x]).tail)
    (hrow : ∀ s, IsSt s → ∑ x ∈ (cands n).filter (SuccX n X s), wtW ωE ωC [x] * H (s ++ [x]).tail ≤ lam * H s)
    (L : ℕ) (hL : K ≤ L) :
    ∑ w ∈ (pats n L).filter (LegalX n X (K + 1)), wtW ωE ωC w ≤
      lam ^ (L - K) * ((∑ s ∈ (pats n K).filter IsSt, wtW ωE ωC s * H s) / Hmin) := by
  set F : ℕ → List (ℕ × Bool) → ℝ := fun L s =>
    ∑ w ∈ (pats n L).filter (fun w => LegalX n X (K + 1) w ∧ w.take K = s), wtW ωE ωC (w.drop K) with hF
  have hwt0 : ∀ w, 0 ≤ wtW ωE ωC w := wtW_nonneg hE hC
  -- the base case `F K s ≤ 1 ≤ H s / Hmin`
  have hbase : ∀ s, IsSt s → F K s ≤ H s / Hmin := by
    intro s hs
    have h1 : F K s ≤ 1 := by
      have hsub : (pats n K).filter (fun w => LegalX n X (K + 1) w ∧ w.take K = s) ⊆ {s} := by
        intro w hw
        rw [Finset.mem_filter, mem_pats] at hw
        rw [Finset.mem_singleton, ← hw.2.2, List.take_of_length_le (le_of_eq hw.1.1)]
      calc F K s ≤ ∑ w ∈ ({s} : Finset (List (ℕ × Bool))), wtW ωE ωC (w.drop K) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => hwt0 _)
        _ = wtW ωE ωC (s.drop K) := Finset.sum_singleton _ _
        _ = 1 := by
            rw [List.drop_of_length_le (le_of_eq (hlen s hs).1)]
            simp [wtW]
    exact le_trans h1 ((one_le_div hHmin).mpr (hpos s hs))
  -- the step `F (L + 1) s ≤ ∑_x ω(x) F L (next)`
  have hstep : ∀ L, K ≤ L → ∀ s, s.length = K →
      F (L + 1) s ≤ ∑ x ∈ (cands n).filter (SuccX n X s), wtW ωE ωC [x] * F L (s ++ [x]).tail := by
    intro L hKL s hsK
    set T : Finset ((ℕ × Bool) × List (ℕ × Bool)) :=
      (((cands n).filter (SuccX n X s)) ×ˢ (pats n L)).filter
        (fun p => LegalX n X (K + 1) p.2 ∧ p.2.take K = (s ++ [p.1]).tail) with hT
    have hR : ∑ p ∈ T, wtW ωE ωC [p.1] * wtW ωE ωC (p.2.drop K) =
        ∑ x ∈ (cands n).filter (SuccX n X s), wtW ωE ωC [x] * F L (s ++ [x]).tail := by
      conv_lhs => rw [hT, Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro x _
      simp only [hF]
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [← hR]
    simp only [hF]
    apply Finset.sum_le_sum_of_injOn (fun w => ((w.drop K).headD (0, false), w.tail))
    · -- injectivity
      intro w1 hw1 w2 hw2 h12
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_pats] at hw1 hw2
      simp only [Prod.mk.injEq] at h12
      obtain ⟨x1, hx1⟩ := split_at (K := K) (w := w1) (by omega)
      obtain ⟨x2, hx2⟩ := split_at (K := K) (w := w2) (by omega)
      rw [hx1, hx2] at h12
      simp only [List.headD_cons] at h12
      rw [← List.take_append_drop K w1, ← List.take_append_drop K w2, hx1, hx2, hw1.2.2, hw2.2.2,
        h12.1, h12.2]
    · -- the image lies in `T`
      intro p hp
      simp only [Finset.mem_image, Finset.mem_filter, mem_pats] at hp
      obtain ⟨w, ⟨⟨hwlen, hwdir⟩, hwleg, hwtake⟩, rfl⟩ := hp
      obtain ⟨x, hx⟩ := split_at (K := K) (w := w) (by omega)
      have hw : w = s ++ x :: w.tail.drop K := by
        conv_lhs => rw [← List.take_append_drop K w]
        rw [hx, hwtake]
      have hsucc : SuccX n X s x := by
        rw [hw] at hwleg
        exact succX_of_legalX hsK hwleg
      have htail : w.tail.take K = (s ++ [x]).tail := by
        have h1 : w.tail.take K = (w.take (K + 1)).tail := by
          cases w with
          | nil => simp
          | cons a t => simp
        rw [h1]
        congr 1
        conv_lhs => rw [hw]
        rw [List.take_append, List.take_of_length_le (by omega), hsK,
          show K + 1 - K = 1 by omega]
        rfl
      simp only [hT, Finset.mem_filter, Finset.mem_product, hx, List.headD_cons, mem_pats]
      refine ⟨⟨⟨?_, hsucc⟩, ?_, ?_⟩, legalX_tail hwleg, htail⟩
      · simp only [cands, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
        exact hsucc.1
      · simp [hwlen]
      · exact fun y hy => hwdir y (List.mem_of_mem_tail hy)
    · -- the weights agree
      intro w hw
      simp only [Finset.mem_filter, mem_pats] at hw
      obtain ⟨x, hx⟩ := split_at (K := K) (w := w) (by omega)
      rw [hx, List.headD_cons, show x :: w.tail.drop K = [x] ++ w.tail.drop K from rfl, wtW_append]
    · -- nonnegativity
      intro p _ _
      exact mul_nonneg (hwt0 _) (hwt0 _)
  -- the bound `F L s ≤ λ^(L-K) H s / Hmin`
  have hbound : ∀ L, K ≤ L → ∀ s, IsSt s → F L s ≤ lam ^ (L - K) * (H s / Hmin) := by
    intro L hL
    induction L, hL using Nat.le_induction with
    | base =>
      intro s hs
      simpa using hbase s hs
    | succ L hKL ih =>
      intro s hs
      calc F (L + 1) s ≤ ∑ x ∈ (cands n).filter (SuccX n X s), wtW ωE ωC [x] * F L (s ++ [x]).tail :=
            hstep L hKL s (hlen s hs).1
        _ ≤ ∑ x ∈ (cands n).filter (SuccX n X s),
              wtW ωE ωC [x] * (lam ^ (L - K) * (H (s ++ [x]).tail / Hmin)) := by
            apply Finset.sum_le_sum
            intro x hx
            exact mul_le_mul_of_nonneg_left (ih _ (hclosed s hs x (Finset.mem_filter.mp hx).2)) (hwt0 _)
        _ = lam ^ (L - K) / Hmin *
              ∑ x ∈ (cands n).filter (SuccX n X s), wtW ωE ωC [x] * H (s ++ [x]).tail := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
        _ ≤ lam ^ (L - K) / Hmin * (lam * H s) :=
            mul_le_mul_of_nonneg_left (hrow s hs) (div_nonneg (pow_nonneg hlam _) hHmin.le)
        _ = lam ^ (L + 1 - K) * (H s / Hmin) := by
            rw [show L + 1 - K = (L - K) + 1 by omega, pow_succ]
            ring
  -- split every legal walk at its first `K` steps
  have hmaps : ∀ w ∈ (pats n L).filter (LegalX n X (K + 1)), w.take K ∈ (pats n K).filter IsSt := by
    intro w hw
    rw [Finset.mem_filter, mem_pats] at hw
    have hlenK : (w.take K).length = K := by
      rw [List.length_take]
      omega
    have hlegK := legalX_take hw.2 K
    rw [Finset.mem_filter, mem_pats]
    exact ⟨⟨hlenK, hlegK.2.1⟩, hstart _ hlenK hlegK⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ s ∈ (pats n K).filter IsSt,
        ∑ w ∈ ((pats n L).filter (LegalX n X (K + 1))).filter (fun w => w.take K = s), wtW ωE ωC w
      = ∑ s ∈ (pats n K).filter IsSt, wtW ωE ωC s * F L s := by
        apply Finset.sum_congr rfl
        intro s _
        have hset : ((pats n L).filter (LegalX n X (K + 1))).filter (fun w => w.take K = s) =
            (pats n L).filter (fun w => LegalX n X (K + 1) w ∧ w.take K = s) := by
          ext w
          simp only [Finset.mem_filter, and_assoc]
        rw [hset]
        simp only [hF]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        rw [Finset.mem_filter] at hw
        conv_lhs => rw [← List.take_append_drop K w]
        rw [wtW_append, hw.2.2]
    _ ≤ ∑ s ∈ (pats n K).filter IsSt, wtW ωE ωC s * (lam ^ (L - K) * (H s / Hmin)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact mul_le_mul_of_nonneg_left (hbound L hL s (Finset.mem_filter.mp hs).2) (hwt0 _)
    _ = lam ^ (L - K) * ((∑ s ∈ (pats n K).filter IsSt, wtW ωE ωC s * H s) / Hmin) := by
        rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring

end QEC
