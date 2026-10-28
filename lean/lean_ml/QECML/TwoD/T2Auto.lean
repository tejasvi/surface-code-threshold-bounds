import QECML.TwoD.T2GenE

/-!
# Weighted automata over the blocks of a code (groundwork for the T2 family factor)

A weighted automaton has states `Q`, a finite token type `T`, an allowed-token relation depending on the state and the
current block, the next state and next block of a token, a weight per token and an end weight per state. The weight
of a word is the product of its token weights times the end weight of its final state.

* `sum_wt_le`: any finite set of allowed words of length at most `N` has total weight at most `V N`.
* `V_le`: any `B : Q → ℝ` with `B ≥ 0` and the Bellman inequality `e q + Σ_t [allowed] g · B (next q) ≤ B q` bounds
  `V N` in every state and from every block.

The family factor of the T2 count uses an automaton with eight states (four grammar states before and after the
witness mark) and the tokens `Move ⊕ Unit` (the unit token is the mark, which does not move the route).
-/

open Finset Classical

namespace QECML

namespace S3Geom

/-- A weighted automaton over the blocks of `G`. -/
structure WAut (G : S3Geom) (Q T : Type) where
  allowed : Q → G.Block → T → Prop
  nq : Q → T → Q
  nb : G.Block → T → G.Block
  g : Q → G.Block → T → ℝ
  e : Q → ℝ

namespace WAut

variable {G : S3Geom} {Q T : Type} [Fintype T] (M : WAut G Q T)

/-- Allowed words. -/
def Gram : Q → G.Block → List T → Prop
  | _, _, [] => True
  | q, cur, t :: ts => M.allowed q cur t ∧ Gram (M.nq q t) (M.nb cur t) ts

/-- The weight of a word: token weights times the end weight of the final state. -/
noncomputable def wt : Q → G.Block → List T → ℝ
  | q, _, [] => M.e q
  | q, cur, t :: ts => M.g q cur t * wt (M.nq q t) (M.nb cur t) ts

/-- The weighted sum over all allowed words of length at most `N`. -/
noncomputable def V : ℕ → Q → G.Block → ℝ
  | 0, q, _ => M.e q
  | N + 1, q, cur => M.e q + ∑ t : T, if M.allowed q cur t then M.g q cur t * V N (M.nq q t) (M.nb cur t) else 0

omit [Fintype T] in
theorem wt_nonneg (hg : ∀ q cur t, 0 ≤ M.g q cur t) (he : ∀ q, 0 ≤ M.e q) :
    ∀ (q : Q) (cur : G.Block) (r : List T), 0 ≤ M.wt q cur r
  | q, _, [] => he q
  | q, cur, t :: ts => mul_nonneg (hg q cur t) (wt_nonneg hg he _ _ ts)

/-- **Automaton bound, combinatorial part.** -/
theorem sum_wt_le (hg : ∀ q cur t, 0 ≤ M.g q cur t) (he : ∀ q, 0 ≤ M.e q) (N : ℕ) :
    ∀ (q : Q) (cur : G.Block) (R : Finset (List T)), (∀ r ∈ R, M.Gram q cur r ∧ r.length ≤ N) →
      ∑ r ∈ R, M.wt q cur r ≤ M.V N q cur := by
  induction N with
  | zero =>
    intro q cur R hR
    have hsub : R ⊆ {[]} := fun r hr => by
      have h := (hR r hr).2
      rw [Finset.mem_singleton]
      exact List.eq_nil_of_length_eq_zero (by omega)
    calc ∑ r ∈ R, M.wt q cur r ≤ ∑ r ∈ ({[]} : Finset (List T)), M.wt q cur r :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => M.wt_nonneg hg he q cur r
      _ = M.V 0 q cur := by rw [Finset.sum_singleton]; rfl
  | succ N ih =>
    intro q cur R hR
    rw [← Finset.sum_fiberwise R List.head? (fun r => M.wt q cur r), Fintype.sum_option]
    have h1 : ∑ r ∈ R with r.head? = none, M.wt q cur r ≤ M.e q := by
      have hsub : (R.filter fun r => r.head? = none) ⊆ {[]} := fun r hr => by
        rw [Finset.mem_filter] at hr
        rw [Finset.mem_singleton]
        exact List.head?_eq_none_iff.1 hr.2
      calc _ ≤ ∑ r ∈ ({[]} : Finset (List T)), M.wt q cur r :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => M.wt_nonneg hg he q cur r
        _ = M.e q := by rw [Finset.sum_singleton]; rfl
    have h2 : ∀ t : T, ∑ r ∈ R with r.head? = some t, M.wt q cur r ≤
        if M.allowed q cur t then M.g q cur t * M.V N (M.nq q t) (M.nb cur t) else 0 := by
      intro t
      have hform : ∀ r ∈ R.filter (fun r => r.head? = some t), r = t :: r.tail := by
        intro r hr
        rw [Finset.mem_filter] at hr
        cases r with
        | nil => simp at hr
        | cons a ts =>
          simp only [List.head?_cons, Option.some.injEq] at hr
          rw [hr.2]
          rfl
      split_ifs with hal
      · have hinj : Set.InjOn List.tail ((R.filter (fun r => r.head? = some t) : Finset (List T)) :
            Set (List T)) := fun r hr r' hr' h => by
          rw [hform r hr, hform r' hr', h]
        calc ∑ r ∈ R with r.head? = some t, M.wt q cur r
            = ∑ r ∈ R with r.head? = some t, M.g q cur t * M.wt (M.nq q t) (M.nb cur t) r.tail := by
              refine Finset.sum_congr rfl fun r hr => ?_
              conv_lhs => rw [hform r hr]
              rfl
          _ = M.g q cur t * ∑ u ∈ (R.filter (fun r => r.head? = some t)).image List.tail,
                M.wt (M.nq q t) (M.nb cur t) u := by
              rw [Finset.sum_image hinj, Finset.mul_sum]
          _ ≤ _ := by
              refine mul_le_mul_of_nonneg_left (ih _ _ _ fun u hu => ?_) (hg q cur t)
              obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hu
              have hrR := (Finset.mem_filter.1 hr).1
              obtain ⟨hgr, hlen⟩ := hR r hrR
              rw [hform r hr] at hgr hlen
              refine ⟨hgr.2, ?_⟩
              simp only [List.length_cons] at hlen
              omega
      · have hempty : R.filter (fun r => r.head? = some t) = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun r hr => ?_
          have hrR := (Finset.mem_filter.1 hr).1
          have hgr := (hR r hrR).1
          rw [hform r hr] at hgr
          exact hal hgr.1
        rw [hempty, Finset.sum_empty]
    calc (∑ r ∈ R with r.head? = none, M.wt q cur r) + ∑ t, ∑ r ∈ R with r.head? = some t, M.wt q cur r
        ≤ M.e q + ∑ t : T, (if M.allowed q cur t then M.g q cur t * M.V N (M.nq q t) (M.nb cur t) else 0) :=
          add_le_add h1 (Finset.sum_le_sum fun t _ => h2 t)
      _ = M.V (N + 1) q cur := rfl

/-- **Automaton bound (Bellman inequality).** -/
theorem V_le (hg : ∀ q cur t, 0 ≤ M.g q cur t) (B : Q → ℝ)
    (hB : ∀ q cur, M.e q + ∑ t : T, (if M.allowed q cur t then M.g q cur t * B (M.nq q t) else 0) ≤ B q)
    (hB0 : ∀ q, 0 ≤ B q) : ∀ (N : ℕ) (q : Q) (cur : G.Block), M.V N q cur ≤ B q := by
  intro N
  induction N with
  | zero =>
    intro q cur
    have h := hB q cur
    have hs : 0 ≤ ∑ t : T, (if M.allowed q cur t then M.g q cur t * B (M.nq q t) else 0) :=
      Finset.sum_nonneg fun t _ => by
        split_ifs
        · exact mul_nonneg (hg q cur t) (hB0 _)
        · exact le_rfl
    show M.e q ≤ B q
    linarith
  | succ N ih =>
    intro q cur
    refine le_trans ?_ (hB q cur)
    show M.e q + ∑ t : T, _ ≤ _
    refine add_le_add le_rfl (Finset.sum_le_sum fun t _ => ?_)
    split_ifs
    · exact mul_le_mul_of_nonneg_left (ih _ _) (hg q cur t)
    · exact le_rfl

end WAut

end S3Geom

end QECML
