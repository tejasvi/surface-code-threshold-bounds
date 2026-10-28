import QEC.Graph.Basic

/-!
# Degrees and odd edges of an edge list

Copied unchanged from an earlier formalization (its exclusion rules), without the weight-based rules of that
file. `oddD P` is the set of detectors of odd degree in the edge list `P` (with multiplicity), `oddE P` the set of
edges used an odd number of times; `bd (oddE P) = oddD P`.
-/

namespace QEC

open Finset
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Degrees and odd edges of an edge list -/

/-- Degree of a vertex in an edge list (with multiplicity). -/
def ldeg (P : List (Sym2 (Vx V))) (x : Vx V) : ℕ := P.countP (fun e => x ∈ e)

/-- The detectors of odd degree in an edge list. -/
def oddD (P : List (Sym2 (Vx V))) : Finset V := univ.filter (fun v => Odd (ldeg P (Vx.det v)))

/-- The edges used an odd number of times. -/
def oddE (P : List (Sym2 (Vx V))) : Finset (Sym2 (Vx V)) := P.toFinset.filter (fun e => Odd (P.count e))

theorem oddE_nil : oddE ([] : List (Sym2 (Vx V))) = ∅ := rfl

theorem oddE_cons (e : Sym2 (Vx V)) (P : List (Sym2 (Vx V))) : oddE (e :: P) = oddE P ∆ {e} := by
  ext e'
  simp only [oddE, mem_filter, List.mem_toFinset, mem_symmDiff, mem_singleton, List.mem_cons, List.count_cons]
  by_cases h : e' = e
  · subst h
    simp
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    constructor
    · intro h _; exact h
    · intro h
      by_cases hm : e' ∈ P
      · exact h hm
      · rw [List.count_eq_zero_of_not_mem hm]; decide
  · simp [h]
    intro _
    simp [Ne.symm h]

theorem ldeg_cons (e : Sym2 (Vx V)) (P : List (Sym2 (Vx V))) (x : Vx V) :
    ldeg (e :: P) x = ldeg P x + if x ∈ e then 1 else 0 := by
  unfold ldeg
  rw [List.countP_cons]
  simp

theorem bd_singleton (e : Sym2 (Vx V)) : bd ({e} : Finset (Sym2 (Vx V))) = univ.filter (fun v => Vx.det v ∈ e) := by
  ext v
  simp only [mem_bd, vdeg, Finset.filter_singleton, mem_filter, mem_univ, true_and]
  split_ifs with h <;> simp [h]

theorem oddD_cons (e : Sym2 (Vx V)) (P : List (Sym2 (Vx V))) : oddD (e :: P) = oddD P ∆ bd {e} := by
  ext v
  rw [bd_singleton]
  simp only [oddD, mem_filter, mem_univ, true_and, mem_symmDiff, ldeg_cons]
  split_ifs with h
  · rw [Nat.odd_add_one]; tauto
  · simp only [add_zero]; tauto

/-- The odd edges of a list have the detector boundary of the list. -/
theorem bd_oddE (P : List (Sym2 (Vx V))) : bd (oddE P) = oddD P := by
  induction P with
  | nil =>
    ext v
    simp [oddE_nil, mem_bd, vdeg, oddD, ldeg]
  | cons e P ih => rw [oddE_cons, bd_symmDiff, ih, oddD_cons]

theorem oddE_subset (P : List (Sym2 (Vx V))) : oddE P ⊆ P.toFinset := Finset.filter_subset _ _

theorem oddE_of_nodup {P : List (Sym2 (Vx V))} (h : P.Nodup) : oddE P = P.toFinset := by
  unfold oddE
  apply Finset.filter_true_of_mem
  intro e he
  rw [List.count_eq_one_of_mem h (List.mem_toFinset.mp he)]
  decide

theorem oddD_perm {P P' : List (Sym2 (Vx V))} (h : P.Perm P') : oddD P = oddD P' := by
  unfold oddD ldeg
  exact Finset.filter_congr (fun v _ => by rw [h.countP_eq])

end QEC
