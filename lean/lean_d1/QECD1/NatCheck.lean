import QECD1.Automaton

/-!
# Kernel-checkable Bellman certificates

A `NatAut n` is an automaton on `Fin n` whose weights and end weights are natural numbers to be read with a common
denominator `Q`. `check A Q B` is a closed Boolean test, evaluated by `decide +kernel`, that the natural numbers
`B q` (read with denominator `Q`) satisfy the Bellman inequalities of `A`:

  `e q * Q + Σ_moves w * B next ≤ B q * Q`   (all quantities natural numbers).

`check_sound` turns a successful check into a bound on the values of the real automaton `toFAut A Q` (weights `w/Q`,
end weights `e/Q`): `val N q ≤ B q / Q` for every word length `N`.
-/

namespace QECD1

/-- An automaton with natural-number weights (denominator fixed separately). -/
structure NatAut (n : ℕ) where
  /-- moves: weight numerator and next state -/
  moves : Fin n → List (ℕ × Fin n)
  /-- end weight numerators -/
  e : Fin n → ℕ

namespace NatAut

variable {n : ℕ}

/-- The Bellman test, one inequality of natural numbers per state. -/
def check (A : NatAut n) (Q : ℕ) (B : Fin n → ℕ) : Bool :=
  (List.finRange n).all fun q => decide (A.e q * Q + ((A.moves q).map fun m => m.1 * B m.2).sum ≤ B q * Q)

/-- The real automaton: weights `w / Q`, end weights `e / Q`. -/
noncomputable def toFAut (A : NatAut n) (Q : ℕ) : FAut (Fin n) where
  moves q := (A.moves q).map fun m => ((m.1 : ℝ) / Q, m.2)
  e q := (A.e q : ℝ) / Q

theorem sum_cast (l : List (ℕ × Fin n)) (B : Fin n → ℕ) (Q : ℕ) :
    ((l.map fun m => ((m.1 : ℝ) / Q, m.2)).map fun m => m.1 * ((B m.2 : ℝ) / Q)).sum =
      (((l.map fun m => m.1 * B m.2).sum : ℕ) : ℝ) / ((Q : ℝ) * Q) := by
  induction l with
  | nil => simp
  | cons m l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul] at ih ⊢
    rw [ih, add_div]
    congr 1
    rw [div_mul_div_comm]

theorem check_sound (A : NatAut n) (Q : ℕ) (hQ : 0 < Q) (B : Fin n → ℕ) (h : A.check Q B = true) :
    ∀ N q, (A.toFAut Q).val N q ≤ (B q : ℝ) / Q := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine FAut.val_le (A.toFAut Q) (fun q => (B q : ℝ) / Q) (fun q => by positivity) ?_ ?_
  · intro q m hm
    simp only [toFAut, List.mem_map] at hm
    obtain ⟨m', _, rfl⟩ := hm
    positivity
  · intro q
    have hq : decide (A.e q * Q + ((A.moves q).map fun m => m.1 * B m.2).sum ≤ B q * Q) = true :=
      List.all_eq_true.1 h q (List.mem_finRange q)
    have hn := of_decide_eq_true hq
    show (A.e q : ℝ) / Q + ((((A.moves q).map fun m => ((m.1 : ℝ) / Q, m.2)).map fun m =>
      m.1 * ((B m.2 : ℝ) / Q)).sum) ≤ (B q : ℝ) / Q
    rw [sum_cast]
    set S := ((A.moves q).map fun m => m.1 * B m.2).sum with hS
    have hr : ((A.e q * Q + S : ℕ) : ℝ) ≤ ((B q * Q : ℕ) : ℝ) := by exact_mod_cast hn
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul] at hr
    rw [div_add_div _ _ (ne_of_gt hQr) (by positivity), div_le_div_iff₀ (by positivity) hQr]
    nlinarith [mul_le_mul_of_nonneg_right hr (by positivity : (0 : ℝ) ≤ (Q : ℝ) * Q)]

end NatAut

end QECD1
