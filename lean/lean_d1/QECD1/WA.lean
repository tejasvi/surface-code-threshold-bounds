import Mathlib

/-!
# Weighted automata with a finite token set per state

States `σ` and tokens `τ`. In state `q` the allowed tokens form the finite set `toks q`; a token `t` leads to
`next q t` and weighs `g q t`; a word that ends in `q` gets the end weight `e q`. The weight of a word is the
product of its token weights times the end weight of its final state. This is the 2D `WAut` (TwoD/T2Auto)
without the block argument, with finite token sets in place of a finite token type (the 3D tokens carry offsets in
`ℤ³`).

* `sum_wt_le`: any finite set of allowed words of length at most `N` has total weight at most `V N q`.
* `V_le`: a function `B ≥ 0` satisfying the Bellman inequality on a set of states `I` that is closed under allowed
  tokens bounds `V N q` for every `q ∈ I`.
-/

namespace QECD1

/-- A weighted automaton with a finite token set per state. -/
structure WA (σ τ : Type) where
  toks : σ → Finset τ
  next : σ → τ → σ
  g : σ → τ → ℝ
  e : σ → ℝ

namespace WA

variable {σ τ : Type} (M : WA σ τ)

/-- Allowed words. -/
def Gram : σ → List τ → Prop
  | _, [] => True
  | q, t :: ts => t ∈ M.toks q ∧ Gram (M.next q t) ts

/-- The weight of a word: token weights times the end weight of the final state. -/
noncomputable def wt : σ → List τ → ℝ
  | q, [] => M.e q
  | q, t :: ts => M.g q t * wt (M.next q t) ts

/-- The weighted sum over all allowed words of length at most `N`. -/
noncomputable def V : ℕ → σ → ℝ
  | 0, q => M.e q
  | N + 1, q => M.e q + ∑ t ∈ M.toks q, M.g q t * V N (M.next q t)

theorem wt_nonneg (hg : ∀ q t, 0 ≤ M.g q t) (he : ∀ q, 0 ≤ M.e q) : ∀ (q : σ) (r : List τ), 0 ≤ M.wt q r
  | q, [] => he q
  | q, t :: ts => mul_nonneg (hg q t) (wt_nonneg hg he _ ts)

/-- **Automaton bound, combinatorial part.** -/
theorem sum_wt_le [DecidableEq τ] (hg : ∀ q t, 0 ≤ M.g q t) (he : ∀ q, 0 ≤ M.e q) (N : ℕ) :
    ∀ (q : σ) (R : Finset (List τ)), (∀ r ∈ R, M.Gram q r ∧ r.length ≤ N) →
      ∑ r ∈ R, M.wt q r ≤ M.V N q := by
  induction N with
  | zero =>
    intro q R hR
    have hsub : R ⊆ {[]} := fun r hr => by
      have h := (hR r hr).2
      rw [Finset.mem_singleton]
      exact List.eq_nil_of_length_eq_zero (by omega)
    calc ∑ r ∈ R, M.wt q r ≤ ∑ r ∈ ({[]} : Finset (List τ)), M.wt q r :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => M.wt_nonneg hg he q r
      _ = M.V 0 q := by rw [Finset.sum_singleton]; rfl
  | succ N ih =>
    intro q R hR
    have hmaps : ∀ r ∈ R, r.head? ∈ insert none ((M.toks q).image some) := by
      intro r hr
      cases r with
      | nil => exact Finset.mem_insert_self _ _
      | cons t ts => exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨t, (hR _ hr).1.1, rfl⟩)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_insert (by simp),
      Finset.sum_image (fun _ _ _ _ h => Option.some.inj h)]
    have h1 : ∑ r ∈ R with r.head? = none, M.wt q r ≤ M.e q := by
      have hsub : (R.filter fun r => r.head? = none) ⊆ {[]} := fun r hr => by
        rw [Finset.mem_filter] at hr
        rw [Finset.mem_singleton]
        exact List.head?_eq_none_iff.1 hr.2
      calc _ ≤ ∑ r ∈ ({[]} : Finset (List τ)), M.wt q r :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => M.wt_nonneg hg he q r
        _ = M.e q := by rw [Finset.sum_singleton]; rfl
    have h2 : ∀ t ∈ M.toks q, ∑ r ∈ R with r.head? = some t, M.wt q r ≤ M.g q t * M.V N (M.next q t) := by
      intro t _
      have hform : ∀ r ∈ R.filter (fun r => r.head? = some t), r = t :: r.tail := by
        intro r hr
        rw [Finset.mem_filter] at hr
        cases r with
        | nil => simp at hr
        | cons a ts =>
          simp only [List.head?_cons, Option.some.injEq] at hr
          rw [hr.2]
          rfl
      have hinj : Set.InjOn List.tail ((R.filter (fun r => r.head? = some t) : Finset (List τ)) :
          Set (List τ)) := fun r hr r' hr' h => by
        rw [hform r hr, hform r' hr', h]
      calc ∑ r ∈ R with r.head? = some t, M.wt q r
          = ∑ r ∈ R with r.head? = some t, M.g q t * M.wt (M.next q t) r.tail := by
            refine Finset.sum_congr rfl fun r hr => ?_
            conv_lhs => rw [hform r hr]
            rfl
        _ = M.g q t * ∑ u ∈ (R.filter (fun r => r.head? = some t)).image List.tail, M.wt (M.next q t) u := by
            rw [Finset.sum_image hinj, Finset.mul_sum]
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left (ih _ _ fun u hu => ?_) (hg q t)
            obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hu
            have hrR := (Finset.mem_filter.1 hr).1
            obtain ⟨hgr, hlen⟩ := hR r hrR
            rw [hform r hr] at hgr hlen
            refine ⟨hgr.2, ?_⟩
            simp only [List.length_cons] at hlen
            omega
    calc (∑ r ∈ R with r.head? = none, M.wt q r) +
          ∑ t ∈ M.toks q, ∑ r ∈ R with r.head? = some t, M.wt q r
        ≤ M.e q + ∑ t ∈ M.toks q, M.g q t * M.V N (M.next q t) :=
          add_le_add h1 (Finset.sum_le_sum h2)
      _ = M.V (N + 1) q := rfl

/-- **Automaton bound (Bellman inequality on an invariant set of states).** -/
theorem V_le (hg : ∀ q t, 0 ≤ M.g q t) (I : σ → Prop) (hI : ∀ q, I q → ∀ t ∈ M.toks q, I (M.next q t))
    (B : σ → ℝ) (hB : ∀ q, I q → M.e q + ∑ t ∈ M.toks q, M.g q t * B (M.next q t) ≤ B q)
    (hB0 : ∀ q, I q → 0 ≤ B q) : ∀ (N : ℕ) (q : σ), I q → M.V N q ≤ B q := by
  intro N
  induction N with
  | zero =>
    intro q hq
    have h := hB q hq
    have hs : 0 ≤ ∑ t ∈ M.toks q, M.g q t * B (M.next q t) :=
      Finset.sum_nonneg fun t ht => mul_nonneg (hg q t) (hB0 _ (hI q hq t ht))
    show M.e q ≤ B q
    linarith
  | succ N ih =>
    intro q hq
    refine le_trans ?_ (hB q hq)
    show M.e q + ∑ t ∈ M.toks q, M.g q t * M.V N (M.next q t) ≤ _
    exact add_le_add le_rfl (Finset.sum_le_sum fun t ht =>
      mul_le_mul_of_nonneg_left (ih _ (hI q hq t ht)) (hg q t))

end WA

end QECD1
