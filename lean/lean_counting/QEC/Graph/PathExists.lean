import QEC.Graph.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Lemma 3.1 (graph part): odd degree at `b1` gives a path to `b2`

If every detector has even degree in a set `R` of edges and `b1` has odd degree, then `R` contains a simple
path from `b1` to `b2`: the component of `b1` has an even number of odd-degree vertices.
-/

namespace QEC

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem even_sum_of_even {ι : Type*} {s : Finset ι} {f : ι → ℕ} (h : ∀ i ∈ s, Even (f i)) :
    Even (∑ i ∈ s, f i) :=
  Finset.sum_induction f Even (fun _ _ => Even.add) ⟨0, rfl⟩ h

open scoped Classical in
/-- In the component of `x` (vertices reachable from `x` along `R`), the degrees sum to an even number. -/
theorem even_sum_vdeg_component {R : Finset (Sym2 (Vx V))} (hdiag : ∀ e ∈ R, ¬ e.IsDiag) (x : Vx V) :
    Even (∑ y ∈ univ.filter ((decGraph R).Reachable x), vdeg R y) := by
  classical
  set K := univ.filter ((decGraph R).Reachable x) with hK
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun y (e : Sym2 (Vx V)) => y ∈ e)
    (s := K) (t := R)
  have h1 : ∑ y ∈ K, vdeg R y = ∑ y ∈ K, #(R.bipartiteAbove (fun y (e : Sym2 (Vx V)) => y ∈ e) y) := by
    apply Finset.sum_congr rfl
    intro y _
    simp only [vdeg, bipartiteAbove]
  rw [h1, hdc]
  apply even_sum_of_even
  intro e he
  induction e using Sym2.ind with
  | _ u w =>
    have huw : u ≠ w := fun h => hdiag _ he (by rw [h, Sym2.mk_isDiag_iff])
    have hadj : (decGraph R).Adj u w := ⟨huw, he⟩
    have hiff : u ∈ K ↔ w ∈ K := by
      simp only [hK, mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
    have hset : K.bipartiteBelow (fun y (e : Sym2 (Vx V)) => y ∈ e) s(u, w) =
        if u ∈ K then {u, w} else ∅ := by
      ext y
      simp only [mem_bipartiteBelow, Sym2.mem_iff]
      split_ifs with hu
      · simp only [mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨hu, Or.inl rfl⟩
          · exact ⟨hiff.mp hu, Or.inr rfl⟩
      · simp only [notMem_empty, iff_false, not_and]
        rintro hy (rfl | rfl)
        · exact hu hy
        · exact hu (hiff.mpr hy)
    rw [hset]
    split_ifs
    · rw [card_pair huw]
      exact even_two
    · simp

/-- **Lemma 3.1 (graph part).** -/
theorem exists_path_of_odd {R : Finset (Sym2 (Vx V))} (hdiag : ∀ e ∈ R, ¬ e.IsDiag)
    (heven : ∀ v : V, Even (vdeg R (.det v))) (hodd : Odd (vdeg R .b1)) :
    ∃ l, IsSPath (decGraph R) .b1 .b2 l := by
  classical
  by_cases hr : (decGraph R).Reachable .b1 .b2
  · obtain ⟨p, hp⟩ := hr.exists_isPath
    refine ⟨p.support, ?_, ?_, p.isChain_adj_support, (SimpleGraph.Walk.isPath_def p).mp hp⟩
    · rw [List.head?_eq_some_head (SimpleGraph.Walk.support_ne_nil p), SimpleGraph.Walk.head_support]
    · rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil p), SimpleGraph.Walk.getLast_support]
  · exfalso
    set K := univ.filter ((decGraph R).Reachable .b1) with hK
    have hev := even_sum_vdeg_component hdiag (.b1 : Vx V)
    have hb1 : (.b1 : Vx V) ∈ K := by simp [hK]
    rw [← Finset.add_sum_erase _ _ hb1] at hev
    have hrest : Even (∑ y ∈ K.erase .b1, vdeg R y) := by
      apply even_sum_of_even
      intro y hy
      rw [mem_erase] at hy
      cases y with
      | det v => exact heven v
      | b1 => exact absurd rfl hy.1
      | b2 => exact absurd (by simpa [hK] using hy.2) hr
    rw [Nat.even_add] at hev
    exact (Nat.not_even_iff_odd.mpr hodd) (hev.mpr hrest)

end QEC
