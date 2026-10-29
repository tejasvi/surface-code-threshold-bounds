import Mathlib

/-!
# Finite weighted automata and Bellman bounds

A finite weighted automaton has states `σ`, for each state a finite list of moves (a weight and the next state), and
an end weight per state. `val A N q` is the total weight of the words of length at most `N` from `q`: the end weight
of `q` plus, for each move, its weight times the value of the next state with one step less.

* `val_le`: a nonnegative `B` satisfying the Bellman inequalities `e q + Σ_moves w * B next ≤ B q` bounds every `val`.
* `val_mono`: with the same moves, larger weights and end weights give larger values.

These are the two facts the refined 3D T2 count needs from automata: the family and excursion factors are values of
automata with real (tilted) weights, which are bounded by automata with rational weights, whose Bellman vectors are
checked by the kernel (`QECD1.NatCheck`).
-/

namespace QECD1

/-- A finite weighted automaton. -/
structure FAut (σ : Type*) where
  /-- the moves from a state: weight and next state -/
  moves : σ → List (ℝ × σ)
  /-- the end weight of a state -/
  e : σ → ℝ

namespace FAut

variable {σ : Type*}

/-- The weight of the words of length at most `N` from a state. -/
noncomputable def val (A : FAut σ) : ℕ → σ → ℝ
  | 0, q => A.e q
  | N + 1, q => A.e q + ((A.moves q).map fun m => m.1 * A.val N m.2).sum

/-- A list sum of products is monotone in the second factor when the first factors are nonnegative. -/
theorem sum_map_mul_le (l : List (ℝ × σ)) (f g : σ → ℝ) (hw : ∀ m ∈ l, 0 ≤ m.1) (hfg : ∀ m ∈ l, f m.2 ≤ g m.2) :
    (l.map fun m => m.1 * f m.2).sum ≤ (l.map fun m => m.1 * g m.2).sum := by
  induction l with
  | nil => simp
  | cons m l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : m.1 * f m.2 ≤ m.1 * g m.2 :=
      mul_le_mul_of_nonneg_left (hfg m List.mem_cons_self) (hw m List.mem_cons_self)
    have h2 := ih (fun m' hm' => hw m' (List.mem_cons_of_mem _ hm')) (fun m' hm' => hfg m' (List.mem_cons_of_mem _ hm'))
    linarith

/-- A list sum of products of nonnegative factors is nonnegative. -/
theorem sum_map_mul_nonneg (l : List (ℝ × σ)) (g : σ → ℝ) (hw : ∀ m ∈ l, 0 ≤ m.1) (hg : ∀ q, 0 ≤ g q) :
    0 ≤ (l.map fun m => m.1 * g m.2).sum := by
  induction l with
  | nil => simp
  | cons m l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : 0 ≤ m.1 * g m.2 := mul_nonneg (hw m List.mem_cons_self) (hg m.2)
    have h2 := ih (fun m' hm' => hw m' (List.mem_cons_of_mem _ hm'))
    linarith

/-- **Bellman bound**: a nonnegative solution of the Bellman inequalities bounds the value of every word length. -/
theorem val_le (A : FAut σ) (B : σ → ℝ) (hB0 : ∀ q, 0 ≤ B q) (hw : ∀ q, ∀ m ∈ A.moves q, 0 ≤ m.1)
    (hB : ∀ q, A.e q + ((A.moves q).map fun m => m.1 * B m.2).sum ≤ B q) : ∀ N q, A.val N q ≤ B q := by
  intro N
  induction N with
  | zero =>
    intro q
    have h := hB q
    have h0 := sum_map_mul_nonneg (A.moves q) B (hw q) hB0
    show A.e q ≤ B q
    linarith
  | succ N ih =>
    intro q
    show A.e q + ((A.moves q).map fun m => m.1 * A.val N m.2).sum ≤ B q
    have h := sum_map_mul_le (A.moves q) (A.val N) B (hw q) (fun m _ => ih m.2)
    linarith [hB q]

/-- Two automata with the same move structure: `A'` has weights and end weights at least those of `A`. -/
def Dominates (A A' : FAut σ) : Prop :=
  (∀ q, A.e q ≤ A'.e q) ∧ ∀ q, List.Forall₂ (fun m m' => m.2 = m'.2 ∧ 0 ≤ m.1 ∧ m.1 ≤ m'.1) (A.moves q) (A'.moves q)

/-- Values are nonnegative when weights and end weights are. -/
theorem val_nonneg (A : FAut σ) (hw : ∀ q, ∀ m ∈ A.moves q, 0 ≤ m.1) (he : ∀ q, 0 ≤ A.e q) :
    ∀ N q, 0 ≤ A.val N q := by
  intro N
  induction N with
  | zero => intro q; exact he q
  | succ N ih =>
    intro q
    show 0 ≤ A.e q + ((A.moves q).map fun m => m.1 * A.val N m.2).sum
    have := sum_map_mul_nonneg (A.moves q) (A.val N) (hw q) ih
    linarith [he q]

theorem forall₂_sum_le {l l' : List (ℝ × σ)} (f f' : σ → ℝ) (hf' : ∀ q, 0 ≤ f' q)
    (h : List.Forall₂ (fun m m' => m.2 = m'.2 ∧ 0 ≤ m.1 ∧ m.1 ≤ m'.1) l l') (hff : ∀ q, f q ≤ f' q) :
    (l.map fun m => m.1 * f m.2).sum ≤ (l'.map fun m => m.1 * f' m.2).sum := by
  induction h with
  | nil => simp
  | @cons m m' l₁ l₂ hm _ ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨h2, h0, h1⟩ := hm
    have : m.1 * f m.2 ≤ m'.1 * f' m'.2 := by
      rw [h2]
      calc m.1 * f m'.2 ≤ m.1 * f' m'.2 := mul_le_mul_of_nonneg_left (hff _) h0
        _ ≤ m'.1 * f' m'.2 := mul_le_mul_of_nonneg_right h1 (hf' _)
    linarith

/-- **Monotonicity**: a dominating automaton (same moves, larger weights and end weights) has larger values. -/
theorem val_mono (A A' : FAut σ) (h : Dominates A A') (hw' : ∀ q, ∀ m ∈ A'.moves q, 0 ≤ m.1)
    (he' : ∀ q, 0 ≤ A'.e q) : ∀ N q, A.val N q ≤ A'.val N q := by
  intro N
  induction N with
  | zero => intro q; exact h.1 q
  | succ N ih =>
    intro q
    show A.e q + ((A.moves q).map fun m => m.1 * A.val N m.2).sum ≤
      A'.e q + ((A'.moves q).map fun m => m.1 * A'.val N m.2).sum
    have hs := forall₂_sum_le (A.val N) (A'.val N) (val_nonneg A' hw' he' N) (h.2 q) ih
    linarith [h.1 q]
