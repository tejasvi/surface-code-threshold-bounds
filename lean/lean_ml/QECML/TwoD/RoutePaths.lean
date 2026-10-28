import QECML.TwoD.Route

/-!
# Simple paths inside a selection

`exists_simple_path`: if `s` is reachable from `e` through blocks of `S` with steps of block distance at most `A`,
there is a list from `e` to `s` of distinct blocks of `S` whose consecutive blocks are distinct and within `A`.
(Via the simple graph of `S` and `Walk.toPath`.)
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-- The graph of a selection: distinct selected blocks within block distance `A`. -/
def selGraph (S : Finset G.Block) (A : ℕ) : SimpleGraph G.Block :=
  SimpleGraph.fromRel fun x y => x ∈ S ∧ y ∈ S ∧ G.blockDist x y ≤ A

theorem selGraph_adj {S : Finset G.Block} {A : ℕ} {x y : G.Block} :
    (selGraph S A).Adj x y ↔ x ≠ y ∧ x ∈ S ∧ y ∈ S ∧ G.blockDist x y ≤ A := by
  simp only [selGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, h.2.1, h.1, by rw [G.blockDist_comm]; exact h.2.2⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

theorem reach_selGraph {S : Finset G.Block} {A : ℕ} {e s : G.Block}
    (h : Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ G.blockDist x y ≤ A) e s) :
    (selGraph S A).Reachable e s := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    by_cases hb : b = c
    · rw [← hb]
      exact ih
    · exact ih.tail (selGraph_adj.2 ⟨hb, hbc⟩)

/-- A simple path from `e` to `s` inside `S` with steps of block distance at most `A`. -/
theorem exists_simple_path {S : Finset G.Block} {A : ℕ} {e s : G.Block} (he : e ∈ S)
    (h : Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ G.blockDist x y ≤ A) e s) :
    ∃ l : List G.Block, l.head? = some e ∧ l.getLast? = some s ∧ l.Nodup ∧ (∀ b ∈ l, b ∈ S) ∧
      List.IsChain (fun x y => x ≠ y ∧ G.blockDist x y ≤ A) l := by
  obtain ⟨w⟩ := reach_selGraph h
  set p := w.toPath
  refine ⟨p.1.support, ?_, ?_, p.isPath.support_nodup, ?_, ?_⟩
  · rw [List.head?_eq_some_head (SimpleGraph.Walk.support_ne_nil _), SimpleGraph.Walk.head_support]
  · rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil _), SimpleGraph.Walk.getLast_support]
  · refine List.IsChain.induction (· ∈ S) _ (SimpleGraph.Walk.isChain_adj_support _)
      (fun x y hxy _ => (selGraph_adj.1 hxy).2.2.1) fun lne => ?_
    rw [SimpleGraph.Walk.head_support]
    exact he
  · refine (SimpleGraph.Walk.isChain_adj_support p.1).imp fun x y hxy => ?_
    have h' := (selGraph_adj (S := S) (A := A)).1 hxy
    exact ⟨h'.1, h'.2.2.2⟩

end S3Geom

end QECML
