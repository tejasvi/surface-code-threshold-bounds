import QEC.Count.TorDefs
import QEC.Count.Counting

/-!
# Counting legal labelled walks with offset-dependent exclusions (dimension 2)

The offset-aware version of `sum_legal_le`: a window is tested at the offset of its first vertex, which a walk
updates step by step (`offAt nxt`). States are pairs (pattern of `K` steps, offset of its first vertex); the state
`(s, o)` has the successors `x` with `SuccG nxt Ex s o x` and the next state `((s ++ [x]).tail, offAt nxt o s 1)`.
If a potential `H ≥ Hmin > 0` on the states satisfies every row `∑_x ω(x) H(next) ≤ λ H(s, o)`, every legal walk of
`K` steps from the offset `o₀` is a state, and the states are closed under legal successors, then the legal walks of
`L ≥ K` steps from `o₀` weigh at most `λ^(L-K) ∑_s ω(s) H(s, o₀) / Hmin`.

The proof is that of `sum_legal_le` with `F_L(s, o) = ∑_{w legal from o, |w| = L, take K w = s} ω(drop K w)`: the
tail of a legal walk from `o` is legal from `offAt nxt o w 1` (`legalG_tail`), which is `offAt nxt o s 1` for `K ≥ 1`.
For `K = 0` the row of the empty state gives `∑_x ω(x) ≤ λ`, and all walks of `L` steps weigh `(∑_x ω(x))^L`.
-/

namespace QEC

open Finset QECComp

namespace CountingT

variable {nxt : ℤ → ℕ → ℤ} {Ex : ℤ → List (ℕ × Bool) → Prop}

theorem offAt_take_of_le (o : ℤ) (w : List (ℕ × Bool)) {i k : ℕ} (h : i ≤ k) :
    offAt nxt o (w.take k) i = offAt nxt o w i := by
  unfold offAt
  rw [List.take_take, Nat.min_eq_left h]

theorem offAt_tail (o : ℤ) (w : List (ℕ × Bool)) (i : ℕ) :
    offAt nxt (offAt nxt o w 1) w.tail i = offAt nxt o w (i + 1) := by
  cases w with
  | nil => simp [offAt]
  | cons x t => simp [offAt, List.take_succ_cons]

theorem legalG_take {M : ℕ} {o : ℤ} {w : List (ℕ × Bool)} (h : LegalG nxt Ex M o w) (k : ℕ) :
    LegalG nxt Ex M o (w.take k) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Counting.selfAv_take h1 k, fun x hx => h2 x (List.mem_of_mem_take hx), ?_⟩
  intro i m hm2 hmM him
  have hlen : (w.take k).length = min k w.length := List.length_take
  have heq : ((w.take k).drop i).take m = (w.drop i).take m := by
    rw [List.drop_take, List.take_take]
    congr 1
    omega
  rw [heq, offAt_take_of_le o w (show i ≤ k by omega)]
  exact h3 i m hm2 hmM (by omega)

theorem legalG_tail {M : ℕ} {o : ℤ} {w : List (ℕ × Bool)} (h : LegalG nxt Ex M o w) :
    LegalG nxt Ex M (offAt nxt o w 1) w.tail := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Counting.selfAv_tail h1, fun x hx => h2 x (List.mem_of_mem_tail hx), ?_⟩
  intro i m hm2 hmM him
  rw [List.drop_tail, offAt_tail]
  rw [List.length_tail] at him
  exact h3 (i + 1) m hm2 hmM (by omega)

/-- A legal walk `s ++ x :: rest` with `|s| = K` from the offset `o`: `x` is a legal successor of `(s, o)`. -/
theorem succG_of_legalG {K : ℕ} {o : ℤ} {s : List (ℕ × Bool)} {x : ℕ × Bool} {rest : List (ℕ × Bool)}
    (hs : s.length = K) (h : LegalG nxt Ex (K + 1) o (s ++ x :: rest)) : SuccG nxt Ex s o x := by
  have htake : (s ++ x :: rest).take (K + 1) = s ++ [x] := by
    rw [List.take_append, List.take_of_length_le (by omega), hs,
      show K + 1 - K = 1 by omega]
    rfl
  have hlegK := legalG_take h (K + 1)
  rw [htake] at hlegK
  have hx4 : x.1 < 4 := by
    have := h.2.1 x (by simp)
    omega
  refine ⟨hx4, hlegK.1, ?_⟩
  intro m hm2 hmM
  rw [hs] at hmM ⊢
  have hwin : (s ++ [x]).drop (K + 1 - m) = ((s ++ [x]).drop (K + 1 - m)).take m := by
    rw [List.take_of_length_le]
    simp [hs]
    omega
  rw [hwin]
  exact hlegK.2.2 (K + 1 - m) m hm2 hmM (by simp [hs]; omega)

/-- All walks of `L` steps weigh `(∑_x ω(x))^L`. -/
theorem sum_pats_wtW (ωE ωC : ℝ) : ∀ L : ℕ,
    ∑ w ∈ pats 2 L, wtW ωE ωC w = (∑ x ∈ cands 2, wtW ωE ωC [x]) ^ L
  | 0 => by simp [pats, wtW]
  | L + 1 => by
    have hinj : Set.InjOn (fun p : (ℕ × Bool) × List (ℕ × Bool) => p.1 :: p.2) ↑(cands 2 ×ˢ pats 2 L) := by
      intro p _ q _ h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      exact Prod.ext h1 h2
    rw [show pats 2 (L + 1) = (cands 2 ×ˢ pats 2 L).image (fun p => p.1 :: p.2) from rfl,
      Finset.sum_image hinj, Finset.sum_product, pow_succ, ← sum_pats_wtW ωE ωC L, mul_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    dsimp only
    rw [show x :: w = [x] ++ w from rfl, Counting.wtW_append]

open scoped Classical in
/-- `sum_legal_leT` for `K ≥ 1`. -/
theorem sum_legal_leT_pos (nxt : ℤ → ℕ → ℤ) (Ex : ℤ → List (ℕ × Bool) → Prop) (K : ℕ) (hK : 1 ≤ K)
    {ωE ωC lam Hmin : ℝ} (hE : 0 ≤ ωE) (hC : 0 ≤ ωC) (hlam : 0 ≤ lam) (hHmin : 0 < Hmin)
    (IsSt : List (ℕ × Bool) → ℤ → Prop) (H : List (ℕ × Bool) → ℤ → ℝ)
    (hlen : ∀ s o, IsSt s o → s.length = K ∧ DirOK 2 s)
    (hpos : ∀ s o, IsSt s o → Hmin ≤ H s o)
    (hclosed : ∀ s o, IsSt s o → ∀ x, SuccG nxt Ex s o x → IsSt (s ++ [x]).tail (offAt nxt o s 1))
    (hrow : ∀ s o, IsSt s o → ∑ x ∈ (cands 2).filter (SuccG nxt Ex s o),
      wtW ωE ωC [x] * H (s ++ [x]).tail (offAt nxt o s 1) ≤ lam * H s o)
    (o0 : ℤ) (hstart : ∀ s, s.length = K → LegalG nxt Ex (K + 1) o0 s → IsSt s o0)
    (Lw : ℕ) (hL : K ≤ Lw) :
    ∑ w ∈ (pats 2 Lw).filter (LegalG nxt Ex (K + 1) o0), wtW ωE ωC w ≤
      lam ^ (Lw - K) * ((∑ s ∈ (pats 2 K).filter (fun s => IsSt s o0), wtW ωE ωC s * H s o0) / Hmin) := by
  -- `F L s o`: the weight of the continuations after the first `K` steps, for walks from the offset `o`
  set F : ℕ → List (ℕ × Bool) → ℤ → ℝ := fun L s o =>
    ∑ w ∈ (pats 2 L).filter (fun w => LegalG nxt Ex (K + 1) o w ∧ w.take K = s), wtW ωE ωC (w.drop K) with hF
  have hwt0 : ∀ w, 0 ≤ wtW ωE ωC w := Counting.wtW_nonneg hE hC
  -- the base case `F K s o ≤ 1 ≤ H s o / Hmin`
  have hbase : ∀ s o, IsSt s o → F K s o ≤ H s o / Hmin := by
    intro s o hs
    have h1 : F K s o ≤ 1 := by
      have hsub : (pats 2 K).filter (fun w => LegalG nxt Ex (K + 1) o w ∧ w.take K = s) ⊆ {s} := by
        intro w hw
        rw [Finset.mem_filter, mem_pats] at hw
        rw [Finset.mem_singleton, ← hw.2.2, List.take_of_length_le (le_of_eq hw.1.1)]
      calc F K s o ≤ ∑ w ∈ ({s} : Finset (List (ℕ × Bool))), wtW ωE ωC (w.drop K) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => hwt0 _)
        _ = wtW ωE ωC (s.drop K) := Finset.sum_singleton _ _
        _ = 1 := by
            rw [List.drop_of_length_le (le_of_eq (hlen s o hs).1)]
            simp [wtW]
    exact le_trans h1 ((one_le_div hHmin).mpr (hpos s o hs))
  -- the step `F (L + 1) s o ≤ ∑_x ω(x) F L (next)`
  have hstep : ∀ L, K ≤ L → ∀ s o, s.length = K →
      F (L + 1) s o ≤ ∑ x ∈ (cands 2).filter (SuccG nxt Ex s o),
        wtW ωE ωC [x] * F L (s ++ [x]).tail (offAt nxt o s 1) := by
    intro L hKL s o hsK
    set T : Finset ((ℕ × Bool) × List (ℕ × Bool)) :=
      (((cands 2).filter (SuccG nxt Ex s o)) ×ˢ (pats 2 L)).filter
        (fun p => LegalG nxt Ex (K + 1) (offAt nxt o s 1) p.2 ∧ p.2.take K = (s ++ [p.1]).tail) with hT
    have hR : ∑ p ∈ T, wtW ωE ωC [p.1] * wtW ωE ωC (p.2.drop K) =
        ∑ x ∈ (cands 2).filter (SuccG nxt Ex s o), wtW ωE ωC [x] * F L (s ++ [x]).tail (offAt nxt o s 1) := by
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
      obtain ⟨x1, hx1⟩ := Counting.split_at (K := K) (w := w1) (by omega)
      obtain ⟨x2, hx2⟩ := Counting.split_at (K := K) (w := w2) (by omega)
      rw [hx1, hx2] at h12
      simp only [List.headD_cons] at h12
      rw [← List.take_append_drop K w1, ← List.take_append_drop K w2, hx1, hx2, hw1.2.2, hw2.2.2,
        h12.1, h12.2]
    · -- the image lies in `T`
      intro p hp
      simp only [Finset.mem_image, Finset.mem_filter, mem_pats] at hp
      obtain ⟨w, ⟨⟨hwlen, hwdir⟩, hwleg, hwtake⟩, rfl⟩ := hp
      obtain ⟨x, hx⟩ := Counting.split_at (K := K) (w := w) (by omega)
      have hw : w = s ++ x :: w.tail.drop K := by
        conv_lhs => rw [← List.take_append_drop K w]
        rw [hx, hwtake]
      have hsucc : SuccG nxt Ex s o x := by
        rw [hw] at hwleg
        exact succG_of_legalG hsK hwleg
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
      have hlegt : LegalG nxt Ex (K + 1) (offAt nxt o s 1) w.tail := by
        rw [← hwtake, offAt_take_of_le o w hK]
        exact legalG_tail hwleg
      simp only [hT, Finset.mem_filter, Finset.mem_product, hx, List.headD_cons, mem_pats]
      refine ⟨⟨⟨?_, hsucc⟩, ?_, ?_⟩, hlegt, htail⟩
      · simp only [cands, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
        have := hsucc.1
        omega
      · simp [hwlen]
      · exact fun y hy => hwdir y (List.mem_of_mem_tail hy)
    · -- the weights agree
      intro w hw
      simp only [Finset.mem_filter, mem_pats] at hw
      obtain ⟨x, hx⟩ := Counting.split_at (K := K) (w := w) (by omega)
      rw [hx, List.headD_cons, show x :: w.tail.drop K = [x] ++ w.tail.drop K from rfl,
        Counting.wtW_append]
    · -- nonnegativity
      intro p _ _
      exact mul_nonneg (hwt0 _) (hwt0 _)
  -- the bound `F L s o ≤ λ^(L-K) H s o / Hmin`
  have hbound : ∀ L, K ≤ L → ∀ s o, IsSt s o → F L s o ≤ lam ^ (L - K) * (H s o / Hmin) := by
    intro L hL
    induction L, hL using Nat.le_induction with
    | base =>
      intro s o hs
      simpa using hbase s o hs
    | succ L hKL ih =>
      intro s o hs
      calc F (L + 1) s o ≤ ∑ x ∈ (cands 2).filter (SuccG nxt Ex s o),
              wtW ωE ωC [x] * F L (s ++ [x]).tail (offAt nxt o s 1) :=
            hstep L hKL s o (hlen s o hs).1
        _ ≤ ∑ x ∈ (cands 2).filter (SuccG nxt Ex s o),
              wtW ωE ωC [x] * (lam ^ (L - K) * (H (s ++ [x]).tail (offAt nxt o s 1) / Hmin)) := by
            apply Finset.sum_le_sum
            intro x hx
            exact mul_le_mul_of_nonneg_left (ih _ _ (hclosed s o hs x (Finset.mem_filter.mp hx).2)) (hwt0 _)
        _ = lam ^ (L - K) / Hmin *
              ∑ x ∈ (cands 2).filter (SuccG nxt Ex s o),
                wtW ωE ωC [x] * H (s ++ [x]).tail (offAt nxt o s 1) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
        _ ≤ lam ^ (L - K) / Hmin * (lam * H s o) :=
            mul_le_mul_of_nonneg_left (hrow s o hs) (div_nonneg (pow_nonneg hlam _) hHmin.le)
        _ = lam ^ (L + 1 - K) * (H s o / Hmin) := by
            rw [show L + 1 - K = (L - K) + 1 by omega, pow_succ]
            ring
  -- split every legal walk at its first `K` steps
  have hmaps : ∀ w ∈ (pats 2 Lw).filter (LegalG nxt Ex (K + 1) o0),
      w.take K ∈ (pats 2 K).filter (fun s => IsSt s o0) := by
    intro w hw
    rw [Finset.mem_filter, mem_pats] at hw
    have hlenK : (w.take K).length = K := by
      rw [List.length_take]
      omega
    have hlegK := legalG_take hw.2 K
    rw [Finset.mem_filter, mem_pats]
    exact ⟨⟨hlenK, hlegK.2.1⟩, hstart _ hlenK hlegK⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ s ∈ (pats 2 K).filter (fun s => IsSt s o0),
        ∑ w ∈ ((pats 2 Lw).filter (LegalG nxt Ex (K + 1) o0)).filter (fun w => w.take K = s), wtW ωE ωC w
      = ∑ s ∈ (pats 2 K).filter (fun s => IsSt s o0), wtW ωE ωC s * F Lw s o0 := by
        apply Finset.sum_congr rfl
        intro s _
        have hset : ((pats 2 Lw).filter (LegalG nxt Ex (K + 1) o0)).filter (fun w => w.take K = s) =
            (pats 2 Lw).filter (fun w => LegalG nxt Ex (K + 1) o0 w ∧ w.take K = s) := by
          ext w
          simp only [Finset.mem_filter, and_assoc]
        rw [hset]
        simp only [hF]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        rw [Finset.mem_filter] at hw
        conv_lhs => rw [← List.take_append_drop K w]
        rw [Counting.wtW_append, hw.2.2]
    _ ≤ ∑ s ∈ (pats 2 K).filter (fun s => IsSt s o0), wtW ωE ωC s * (lam ^ (Lw - K) * (H s o0 / Hmin)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact mul_le_mul_of_nonneg_left (hbound Lw hL s o0 (Finset.mem_filter.mp hs).2) (hwt0 _)
    _ = lam ^ (Lw - K) * ((∑ s ∈ (pats 2 K).filter (fun s => IsSt s o0), wtW ωE ωC s * H s o0) / Hmin) := by
        rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring

end CountingT

open CountingT in
open scoped Classical in
/-- **Counting with memory and offset-dependent exclusions.** -/
theorem sum_legal_leT (nxt : ℤ → ℕ → ℤ) (Ex : ℤ → List (ℕ × Bool) → Prop) (K : ℕ) {ωE ωC lam Hmin : ℝ}
    (hE : 0 ≤ ωE) (hC : 0 ≤ ωC) (hlam : 0 ≤ lam) (hHmin : 0 < Hmin)
    (IsSt : List (ℕ × Bool) → ℤ → Prop) (H : List (ℕ × Bool) → ℤ → ℝ)
    (hlen : ∀ s o, IsSt s o → s.length = K ∧ DirOK 2 s)
    (hpos : ∀ s o, IsSt s o → Hmin ≤ H s o)
    (hclosed : ∀ s o, IsSt s o → ∀ x, SuccG nxt Ex s o x → IsSt (s ++ [x]).tail (offAt nxt o s 1))
    (hrow : ∀ s o, IsSt s o → ∑ x ∈ (cands 2).filter (SuccG nxt Ex s o),
      wtW ωE ωC [x] * H (s ++ [x]).tail (offAt nxt o s 1) ≤ lam * H s o)
    (o0 : ℤ) (hstart : ∀ s, s.length = K → LegalG nxt Ex (K + 1) o0 s → IsSt s o0)
    (Lw : ℕ) (hL : K ≤ Lw) :
    ∑ w ∈ (pats 2 Lw).filter (LegalG nxt Ex (K + 1) o0), wtW ωE ωC w ≤
      lam ^ (Lw - K) * ((∑ s ∈ (pats 2 K).filter (fun s => IsSt s o0), wtW ωE ωC s * H s o0) / Hmin) := by
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · -- `K = 0`: the row of the empty state bounds `∑_x ω(x)` by `λ`
    subst hK0
    have hleg0 : LegalG nxt Ex (0 + 1) o0 [] := by
      refine ⟨by simp [SelfAv], fun x hx => by simp at hx, ?_⟩
      intro i m hm2 _ him
      simp only [List.length_nil] at him
      omega
    have hst0 : IsSt [] o0 := hstart [] rfl hleg0
    have hH0 : 0 < H [] o0 := lt_of_lt_of_le hHmin (hpos [] o0 hst0)
    have hsa : ∀ x ∈ cands 2, SuccG nxt Ex [] o0 x := by
      rintro ⟨d, l⟩ hx
      have hd : d < 4 := by
        simp only [cands, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true] at hx
        omega
      refine ⟨hd, ?_, fun m hm2 hm1 => absurd hm2 (by simp at hm1; omega)⟩
      rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;>
        cases l <;> (unfold SelfAv; decide)
    have hfilt : (cands 2).filter (SuccG nxt Ex [] o0) = cands 2 := Finset.filter_true_of_mem hsa
    have hrow0 := hrow [] o0 hst0
    have hoff : offAt nxt o0 [] 1 = o0 := by simp [offAt]
    simp only [hfilt, List.nil_append, List.tail_cons, hoff] at hrow0
    rw [← Finset.sum_mul] at hrow0
    have hS : ∑ x ∈ cands 2, wtW ωE ωC [x] ≤ lam := le_of_mul_le_mul_right hrow0 hH0
    have hS0 : 0 ≤ ∑ x ∈ cands 2, wtW ωE ωC [x] :=
      Finset.sum_nonneg (fun x _ => Counting.wtW_nonneg hE hC _)
    have hRHS : (∑ s ∈ (pats 2 0).filter (fun s => IsSt s o0), wtW ωE ωC s * H s o0) = H [] o0 := by
      rw [show pats 2 0 = {[]} from rfl, Finset.filter_singleton]
      simp [hst0, wtW]
    rw [hRHS, Nat.sub_zero]
    calc ∑ w ∈ (pats 2 Lw).filter (LegalG nxt Ex (0 + 1) o0), wtW ωE ωC w
        ≤ ∑ w ∈ pats 2 Lw, wtW ωE ωC w :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun w _ _ => Counting.wtW_nonneg hE hC w)
      _ = (∑ x ∈ cands 2, wtW ωE ωC [x]) ^ Lw := sum_pats_wtW ωE ωC Lw
      _ ≤ lam ^ Lw := pow_le_pow_left₀ hS0 hS Lw
      _ ≤ lam ^ Lw * (H [] o0 / Hmin) :=
          le_mul_of_one_le_right (pow_nonneg hlam _) ((one_le_div hHmin).mpr (hpos [] o0 hst0))
  · exact sum_legal_leT_pos nxt Ex K hKpos hE hC hlam hHmin IsSt H hlen hpos hclosed hrow o0 hstart Lw hL

end QEC
