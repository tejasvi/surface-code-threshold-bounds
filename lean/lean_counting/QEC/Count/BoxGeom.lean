import QEC.Count.Defs
import QEC.Count.Geom

/-!
# Geometry of the box code

Positions of checks, adjacency (ℓ¹ distance `1`) as unit steps, the directions of a path of checks, and the labelled
pattern of a path (`patOf`) with its walk (`walkPts_patOf`).
-/

namespace QEC

open Finset QECComp

variable {n : ℕ} {N : Fin n → ℕ}

@[simp] theorem length_pos (v : BoxV n N) : (pos v).length = n := by simp [pos]

theorem getD_pos (v : BoxV n N) (i : Fin n) : (pos v).getD i 0 = ((v i : ℕ) : ℤ) := by
  simp [pos, List.getD_eq_getElem?_getD]

theorem pos_injective : Function.Injective (pos (n := n) (N := N)) := by
  intro u v h
  funext i
  have := congrArg (fun l => l.getD i 0) h
  simp only [getD_pos] at this
  exact Fin.ext (by exact_mod_cast this)

theorem ofFn_getD {x : List ℤ} (hx : x.length = n) : List.ofFn (fun i : Fin n => x.getD i 0) = x := by
  subst hx
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem getD_addP : ∀ (a b : List ℤ) (i : ℕ), i < a.length → i < b.length →
    (addP a b).getD i 0 = a.getD i 0 + b.getD i 0
  | [], _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, 0, _, _ => by simp [addP]
  | a :: as, b :: bs, i + 1, h1, h2 => by
    simp only [addP, List.getD_cons_succ]
    exact getD_addP as bs i (by simpa using h1) (by simpa using h2)

theorem getD_vecOf (n d i : ℕ) (hi : i < n) :
    (vecOf n d).getD i 0 = if i = d / 2 then (if d % 2 = 0 then (1 : ℤ) else -1) else 0 := by
  simp [vecOf, List.getD_eq_getElem?_getD, hi]

/-- Two lists of `n` integers are equal iff their coordinates are. -/
theorem list_ext_getD {x y : List ℤ} (hx : x.length = n) (hy : y.length = n)
    (h : ∀ i < n, x.getD i 0 = y.getD i 0) : x = y := by
  apply List.ext_getElem (by rw [hx, hy])
  intro i h1 h2
  have := h i (by omega)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] using this

/-- A list of `n` integers inside the box is the position of a check. -/
theorem exists_pos {x : List ℤ} (hx : x.length = n) (hin : ∀ i : Fin n, 0 ≤ x.getD i 0 ∧ x.getD i 0 < N i) :
    ∃ v : BoxV n N, pos v = x := by
  refine ⟨fun i => ⟨(x.getD i 0).toNat, by have := hin i; omega⟩, ?_⟩
  apply list_ext_getD (length_pos _) hx
  intro i hi
  rw [getD_pos _ ⟨i, hi⟩]
  have := hin ⟨i, hi⟩
  simp only at this ⊢
  omega

/-- Adjacent checks (ℓ¹ distance `1`) differ by a unit vector. -/
theorem l1B_eq_one_iff (u v : BoxV n N) : l1B u v = 1 ↔ ∃ d < 2 * n, pos v = addP (pos u) (vecOf n d) := by
  constructor
  · intro h
    unfold l1B at h
    obtain ⟨i, -, hi⟩ : ∃ i ∈ (univ : Finset (Fin n)), Int.natAbs ((u i : ℤ) - (v i : ℤ)) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      rw [Finset.sum_eq_zero (fun i hi => hcon i hi)] at h
      exact absurd h (by norm_num)
    have hsum := Finset.add_sum_erase univ (fun i => Int.natAbs ((u i : ℤ) - (v i : ℤ))) (mem_univ i)
    rw [h] at hsum
    have hi1 : Int.natAbs ((u i : ℤ) - (v i : ℤ)) = 1 := by omega
    have hrest : ∀ j ∈ univ.erase i, Int.natAbs ((u j : ℤ) - (v j : ℤ)) = 0 := by
      have h0 : ∑ j ∈ univ.erase i, Int.natAbs ((u j : ℤ) - (v j : ℤ)) = 0 := by omega
      exact (Finset.sum_eq_zero_iff.mp h0)
    refine ⟨2 * i + (if (v i : ℤ) > (u i : ℤ) then 0 else 1), by split_ifs <;> omega, ?_⟩
    apply list_ext_getD (length_pos v) (by simp)
    intro j hj
    rw [getD_addP _ _ _ (by simp [hj]) (by simp [hj]), getD_pos v ⟨j, hj⟩, getD_pos u ⟨j, hj⟩,
      getD_vecOf n _ j hj]
    by_cases hji : j = (i : ℕ)
    · have hfin : (⟨j, hj⟩ : Fin n) = i := Fin.ext hji
      rw [hfin]
      subst hji
      rcases Int.natAbs_eq_iff.mp hi1 with h1 | h1
      · have hng : ¬ (((v i : ℕ) : ℤ) > ((u i : ℕ) : ℤ)) := by push_cast at h1 ⊢; omega
        simp only [hng, if_false]
        rw [if_pos (by omega), if_neg (by omega)]
        push_cast at h1
        omega
      · have hg : ((v i : ℕ) : ℤ) > ((u i : ℕ) : ℤ) := by push_cast at h1 ⊢; omega
        simp only [hg, if_true]
        rw [if_pos (by omega), if_pos (by omega)]
        push_cast at h1
        omega
    · have hdiv : (2 * (i : ℕ) + (if (v i : ℤ) > (u i : ℤ) then 0 else 1)) / 2 ≠ j := by
        split_ifs <;> omega
      rw [if_neg (fun h => hdiv h.symm)]
      have := Int.natAbs_eq_zero.mp (hrest ⟨j, hj⟩ (by simp [Fin.ext_iff, hji]))
      omega
  · rintro ⟨d, hd, h⟩
    unfold l1B
    have hcoord : ∀ j : Fin n, ((v j : ℕ) : ℤ) = ((u j : ℕ) : ℤ) +
        (if (j : ℕ) = d / 2 then (if d % 2 = 0 then (1 : ℤ) else -1) else 0) := by
      intro j
      have := congrArg (fun l => l.getD j 0) h
      rw [getD_pos, getD_addP _ _ _ (by simp) (by simp), getD_pos, getD_vecOf n d j j.2] at this
      exact this
    have hax : d / 2 < n := by omega
    rw [← Finset.add_sum_erase univ _ (mem_univ (⟨d / 2, hax⟩ : Fin n))]
    rw [Finset.sum_eq_zero]
    · have := hcoord ⟨d / 2, hax⟩
      simp only [if_true] at this
      have h2 : ((u ⟨d / 2, hax⟩ : ℕ) : ℤ) - ((v ⟨d / 2, hax⟩ : ℕ) : ℤ) = -1 ∨
          ((u ⟨d / 2, hax⟩ : ℕ) : ℤ) - ((v ⟨d / 2, hax⟩ : ℕ) : ℤ) = 1 := by split_ifs at this <;> omega
      rcases h2 with h2 | h2 <;> rw [h2] <;> rfl
    · intro j hj
      have hne : (j : ℕ) ≠ d / 2 := by
        intro h'
        apply (Finset.mem_erase.mp hj).1
        exact Fin.ext h'
      have := hcoord j
      rw [if_neg hne] at this
      rw [show ((u j : ℕ) : ℤ) - ((v j : ℕ) : ℤ) = 0 by omega]
      rfl

/-- The direction from a check to an adjacent check. -/
noncomputable def dirOf (u v : BoxV n N) : ℕ :=
  open Classical in if h : ∃ d < 2 * n, pos v = addP (pos u) (vecOf n d) then Classical.choose h else 0

theorem dirOf_spec {u v : BoxV n N} (h : l1B u v = 1) :
    dirOf u v < 2 * n ∧ pos v = addP (pos u) (vecOf n (dirOf u v)) := by
  have h' := (l1B_eq_one_iff u v).mp h
  simp only [dirOf, dif_pos h']
  exact Classical.choose_spec h'

/-- The labelled pattern of a path of checks (label `true` = C-edge = not in `S`). -/
noncomputable def patOf (S : Finset (Sym2 (Vx (BoxV n N)))) : List (BoxV n N) → List (ℕ × Bool)
  | u :: v :: rest => (dirOf u v, decide (s(Vx.det u, Vx.det v) ∉ S)) :: patOf S (v :: rest)
  | _ => []

/-- Consecutive checks of the list are adjacent. -/
def AdjChain : List (BoxV n N) → Prop
  | u :: v :: rest => l1B u v = 1 ∧ AdjChain (v :: rest)
  | _ => True

theorem length_patOf (S : Finset (Sym2 (Vx (BoxV n N)))) :
    ∀ vs : List (BoxV n N), (patOf S vs).length = vs.length - 1
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by simp [patOf, length_patOf S (v :: rest)]

theorem dirOK_patOf (S : Finset (Sym2 (Vx (BoxV n N)))) :
    ∀ vs : List (BoxV n N), AdjChain vs → DirOK n (patOf S vs)
  | [], _ => by simp [patOf, DirOK]
  | [_], _ => by simp [patOf, DirOK]
  | u :: v :: rest, h => by
    intro x hx
    simp only [patOf, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (dirOf_spec h.1).1
    · exact dirOK_patOf S (v :: rest) h.2 x hx

/-- The walk of the pattern of a path of checks, from the first check, is the list of positions. -/
theorem walkPts_patOf (S : Finset (Sym2 (Vx (BoxV n N)))) :
    ∀ (v0 : BoxV n N) (rest : List (BoxV n N)), AdjChain (v0 :: rest) →
      walkPts n (pos v0) ((patOf S (v0 :: rest)).map Prod.fst) = (v0 :: rest).map pos
  | v0, [], _ => by simp [patOf]
  | v0, v :: rest, h => by
    simp only [patOf, List.map_cons, walkPts_cons, List.cons.injEq, true_and]
    rw [← (dirOf_spec h.1).2]
    exact walkPts_patOf S v rest h.2

end QEC
