import QECCountComp.Core
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.Ring

/-!
# Basic facts about the lattice geometry of the computational core

Lengths, the algebra of `addP` on lists of equal length, translation of walks.
-/

namespace QECComp

@[simp] theorem length_zeros (n : ℕ) : (zeros n).length = n := List.length_replicate

@[simp] theorem length_vecOf (n d : ℕ) : (vecOf n d).length = n := by simp [vecOf]

@[simp] theorem length_addP : ∀ (a b : List ℤ), (addP a b).length = min a.length b.length
  | [], _ => by simp [addP]
  | _ :: _, [] => by simp [addP]
  | _ :: as, _ :: bs => by simp [addP, length_addP as bs, Nat.succ_min_succ]

theorem addP_comm : ∀ (a b : List ℤ), addP a b = addP b a
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by simp [addP, add_comm, addP_comm as bs]

theorem addP_assoc : ∀ (a b c : List ℤ), addP (addP a b) c = addP a (addP b c)
  | [], _, _ => by simp [addP]
  | _ :: _, [], _ => by simp [addP]
  | _ :: _, _ :: _, [] => by simp [addP]
  | a :: as, b :: bs, c :: cs => by simp [addP, add_assoc, addP_assoc as bs cs]

theorem addP_zeros : ∀ (a : List ℤ), addP a (zeros a.length) = a
  | [] => rfl
  | a :: as => by
    have := addP_zeros as
    simp only [zeros, List.length_cons, List.replicate_succ, addP, add_zero, List.cons.injEq, true_and] at this ⊢
    exact this

theorem zeros_addP (a : List ℤ) : addP (zeros a.length) a = a := by rw [addP_comm, addP_zeros]

theorem addP_left_cancel : ∀ {a b c : List ℤ}, b.length = a.length → c.length = a.length →
    addP a b = addP a c → b = c
  | [], [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _, _ => by simp at h
  | [], _, _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | _ :: _, _, [], _, h, _ => by simp at h
  | a :: as, b :: bs, c :: cs, hb, hc, h => by
    simp only [addP, List.cons.injEq, add_right_inj] at h
    simp only [List.length_cons, add_left_inj] at hb hc
    rw [h.1, addP_left_cancel hb hc h.2]

@[simp] theorem walkPts_nil (n : ℕ) (o : List ℤ) : walkPts n o [] = [o] := rfl

@[simp] theorem walkPts_cons (n : ℕ) (o : List ℤ) (d : ℕ) (ds : List ℕ) :
    walkPts n o (d :: ds) = o :: walkPts n (addP o (vecOf n d)) ds := rfl

@[simp] theorem length_walkPts (n : ℕ) : ∀ (o : List ℤ) (ds : List ℕ), (walkPts n o ds).length = ds.length + 1
  | _, [] => rfl
  | o, _ :: ds => by simp [length_walkPts n _ ds]

/-- Every point of a walk from a point with `n` coordinates has `n` coordinates. -/
theorem length_of_mem_walkPts {n : ℕ} : ∀ {o : List ℤ} {ds : List ℕ} {x : List ℤ}, o.length = n →
    x ∈ walkPts n o ds → x.length = n
  | o, [], x, ho, hx => by simp at hx; rw [hx, ho]
  | o, d :: ds, x, ho, hx => by
    simp only [walkPts_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ho
    · exact length_of_mem_walkPts (by simp [ho]) hx

/-- Translation of walks: the walk from `o + o'` is the walk from `o'` translated by `o`. -/
theorem walkPts_translate {n : ℕ} : ∀ {o o' : List ℤ} (ds : List ℕ), o.length = n → o'.length = n →
    walkPts n (addP o o') ds = (walkPts n o' ds).map (addP o)
  | o, o', [], _, _ => by simp
  | o, o', d :: ds, ho, ho' => by
    simp only [walkPts_cons, List.map_cons, List.cons.injEq, true_and]
    rw [addP_assoc]
    exact walkPts_translate ds ho (by simp [ho'])

/-- The walk from `o` is the walk from the origin translated by `o`. -/
theorem walkPts_eq_map {n : ℕ} {o : List ℤ} (ho : o.length = n) (ds : List ℕ) :
    walkPts n o ds = (walkPts n (zeros n) ds).map (addP o) := by
  have h := walkPts_translate (o := o) (o' := zeros n) ds ho (length_zeros n)
  rw [← ho, addP_zeros] at h
  rw [← ho]
  exact h

/-- Translation by a point with `n` coordinates is injective on points with `n` coordinates. -/
theorem addP_injOn {n : ℕ} {o : List ℤ} (ho : o.length = n) {x y : List ℤ} (hx : x.length = n)
    (hy : y.length = n) (h : addP o x = addP o y) : x = y :=
  addP_left_cancel (by rw [hx, ho]) (by rw [hy, ho]) h

end QECComp
