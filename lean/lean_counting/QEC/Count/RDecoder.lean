import QEC.Count.RDefs
import QEC.Count.IID
import QEC.Graph.PathExists
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Region codes: the failure path, half-weight, the exchange lemma, ML

As `Decoder.lean` for the region codes of `RDefs.lean`.

* `failure_pathR`: a failing minimum-weight correction gives a simple path in `E ∆ C` from a side-1 outer point
  through checks only to a side-2 outer point (when the graph has no edge between two outer points).
* `half_weight_unifR`, `exists_phiMinFailR`.
* `exchangeR`: as `exchange`, with the class condition "the alternative has an even number of edge ends at side-1
  outer points" in place of "no edge at `b1`".
* `PfailMLR_le_PfailMWR`.
-/

namespace QEC

open Finset
open scoped symmDiff

namespace RDecoder

/-! ## Odd edges of an edge list, for any vertex type -/

section Gen

variable {X : Type*} [DecidableEq X]

/-- The edges used an odd number of times. -/
def roddE (P : List (Sym2 X)) : Finset (Sym2 X) := P.toFinset.filter (fun e => Odd (P.count e))

theorem roddE_nil : roddE ([] : List (Sym2 X)) = ∅ := rfl

theorem roddE_cons (e : Sym2 X) (P : List (Sym2 X)) : roddE (e :: P) = roddE P ∆ {e} := by
  ext e'
  simp only [roddE, mem_filter, List.mem_toFinset, mem_symmDiff, mem_singleton, List.mem_cons, List.count_cons]
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

theorem roddE_subset (P : List (Sym2 X)) : roddE P ⊆ P.toFinset := Finset.filter_subset _ _

/-- The symmetric difference of disjoint sets is their union. -/
theorem rsymmDiff_eq_union {α : Type*} [DecidableEq α] {A B : Finset α} (h : Disjoint A B) : A ∆ B = A ∪ B := by
  ext e
  simp only [Finset.mem_symmDiff, Finset.mem_union]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (h1 | h1)
    · exact Or.inl ⟨h1, fun h2 => Finset.disjoint_left.mp h h1 h2⟩
    · exact Or.inr ⟨h1, fun h2 => Finset.disjoint_left.mp h h2 h1⟩

theorem roddE_of_nodup {P : List (Sym2 X)} (h : P.Nodup) : roddE P = P.toFinset := by
  unfold roddE
  apply Finset.filter_true_of_mem
  intro e he
  rw [List.count_eq_one_of_mem h (List.mem_toFinset.mp he)]
  decide

theorem vdeg_singleton (e : Sym2 X) (x : X) : vdeg {e} x = if x ∈ e then 1 else 0 := by
  unfold vdeg
  rw [Finset.filter_singleton]
  split_ifs <;> simp

/-- The degree parity of the odd edges is that of the list. -/
theorem odd_vdeg_roddE (P : List (Sym2 X)) (x : X) :
    Odd (vdeg (roddE P) x) ↔ Odd (P.countP (fun e => x ∈ e)) := by
  induction P with
  | nil => simp [roddE_nil, vdeg]
  | cons e P ih =>
    rw [roddE_cons, odd_vdeg_symmDiff, ih, vdeg_singleton, List.countP_cons]
    by_cases hx : x ∈ e
    · simp [hx, Nat.odd_add_one]
    · simp [hx]

end Gen

/-! ## Even degree sums over sets closed under adjacency -/

theorem even_sum_of_evenR {ι : Type*} {s : Finset ι} {f : ι → ℕ} (h : ∀ i ∈ s, Even (f i)) :
    Even (∑ i ∈ s, f i) :=
  Finset.sum_induction f Even (fun _ _ => Even.add) ⟨0, rfl⟩ h

/-- In a set closed under adjacency, the degrees sum to an even number. -/
theorem even_sum_vdeg_closed {X : Type*} [DecidableEq X] {R : Finset (Sym2 X)} (hdiag : ∀ e ∈ R, ¬ e.IsDiag)
    (A : Finset X) (hA : ∀ u w, (decGraph R).Adj u w → (u ∈ A ↔ w ∈ A)) : Even (∑ y ∈ A, vdeg R y) := by
  classical
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun y (e : Sym2 X) => y ∈ e)
    (s := A) (t := R)
  have h1 : ∑ y ∈ A, vdeg R y = ∑ y ∈ A, #(R.bipartiteAbove (fun y (e : Sym2 X) => y ∈ e) y) := by
    apply Finset.sum_congr rfl
    intro y _
    simp only [vdeg, bipartiteAbove]
  rw [h1, hdc]
  apply even_sum_of_evenR
  intro e he
  induction e using Sym2.ind with
  | _ u w =>
    have huw : u ≠ w := fun h => hdiag _ he (by rw [h, Sym2.mk_isDiag_iff])
    have hadj : (decGraph R).Adj u w := ⟨huw, he⟩
    have hiff : u ∈ A ↔ w ∈ A := hA u w hadj
    have hset : A.bipartiteBelow (fun y (e : Sym2 X) => y ∈ e) s(u, w) =
        if u ∈ A then {u, w} else ∅ := by
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

end RDecoder

open RDecoder

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ## Region facts -/

namespace RDecoder

/-- `RVx V W ≃ V ⊕ W`. -/
def rvxEquiv : RVx V W ≃ V ⊕ W where
  toFun x := match x with
    | RVx.chk v => Sum.inl v
    | RVx.out w => Sum.inr w
  invFun s := match s with
    | Sum.inl v => RVx.chk v
    | Sum.inr w => RVx.out w
  left_inv x := by cases x <;> rfl
  right_inv s := by cases s <;> rfl

theorem sum_rvx (f : RVx V W → ℕ) : ∑ x, f x = ∑ v, f (RVx.chk v) + ∑ w, f (RVx.out w) := by
  rw [← Fintype.sum_equiv rvxEquiv.symm (fun s => f (rvxEquiv.symm s)) f (fun _ => rfl), Fintype.sum_sum_type]
  rfl

theorem rbd_symmDiff (C D : Finset (Sym2 (RVx V W))) : rbd (C ∆ D) = rbd C ∆ rbd D := by
  ext v
  simp only [rbd, mem_filter, mem_univ, true_and, mem_symmDiff, odd_vdeg_symmDiff]
  tauto

theorem rbd_roddE (P : List (Sym2 (RVx V W))) : rbd (roddE P) = roddD P := by
  ext v
  unfold rbd roddD rldeg
  rw [mem_filter, mem_filter]
  simp only [mem_univ, true_and]
  exact odd_vdeg_roddE P (RVx.chk v)

theorem side1deg_symmDiff_add (side : W → Bool) (C D : Finset (Sym2 (RVx V W))) :
    side1deg side (C ∆ D) + 2 * side1deg side (C ∩ D) = side1deg side C + side1deg side D := by
  unfold side1deg
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  exact vdeg_symmDiff C D (RVx.out w)

theorem odd_side1deg_symmDiff (side : W → Bool) (C D : Finset (Sym2 (RVx V W))) :
    Odd (side1deg side (C ∆ D)) ↔ ¬ (Odd (side1deg side C) ↔ Odd (side1deg side D)) := by
  have h := side1deg_symmDiff_add side C D
  constructor
  · intro hodd
    rcases Nat.even_or_odd (side1deg side C) with hC | hC <;>
      rcases Nat.even_or_odd (side1deg side D) with hD | hD
    · exfalso; obtain ⟨k, hk⟩ := hodd; obtain ⟨a, ha⟩ := hC; obtain ⟨b, hb⟩ := hD; omega
    · simp only [Nat.not_odd_iff_even.mpr hC, hD, iff_true, not_false_eq_true]
    · simp only [hC, Nat.not_odd_iff_even.mpr hD, iff_false, not_true_eq_false, not_false_eq_true]
    · exfalso; obtain ⟨k, hk⟩ := hodd; obtain ⟨a, ha⟩ := hC; obtain ⟨b, hb⟩ := hD; omega
  · intro hne
    rcases Nat.even_or_odd (side1deg side C) with hC | hC <;>
      rcases Nat.even_or_odd (side1deg side D) with hD | hD
    · exact absurd ⟨fun h' => absurd h' (Nat.not_odd_iff_even.mpr hC),
        fun h' => absurd h' (Nat.not_odd_iff_even.mpr hD)⟩ hne
    · obtain ⟨a, ha⟩ := hC; obtain ⟨b, hb⟩ := hD
      exact ⟨a + b - side1deg side (C ∩ D), by omega⟩
    · obtain ⟨a, ha⟩ := hC; obtain ⟨b, hb⟩ := hD
      exact ⟨a + b - side1deg side (C ∩ D), by omega⟩
    · exact absurd ⟨fun _ => hD, fun _ => hC⟩ hne

/-- Edges without outer points do not change `side1deg`. -/
theorem side1deg_eq_zero (side : W → Bool) {T : Finset (Sym2 (RVx V W))} (hT : ∀ e ∈ T, ∀ w : W, RVx.out w ∉ e) :
    side1deg side T = 0 := by
  unfold side1deg
  apply Finset.sum_eq_zero
  intro w _
  unfold vdeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  exact hT e he w

/-- The side-1 parity of the odd edges of a list. -/
theorem odd_side1deg_roddE (side : W → Bool) (P : List (Sym2 (RVx V W))) :
    Odd (side1deg side (roddE P)) ↔ Odd (∑ w ∈ univ.filter (fun w => side w = true), rldeg P (RVx.out w)) := by
  have hw : ∀ w, vdeg (roddE P) (RVx.out w) % 2 = rldeg P (RVx.out w) % 2 := by
    intro w
    have h := odd_vdeg_roddE P (RVx.out w)
    unfold rldeg
    rcases Nat.even_or_odd (vdeg (roddE P) (RVx.out w)) with h1 | h1
    · have h2 : ¬ Odd (P.countP (fun e => RVx.out w ∈ e)) := fun h2 => (Nat.not_odd_iff_even.mpr h1) (h.mpr h2)
      rw [Nat.not_odd_iff_even] at h2
      rw [Nat.even_iff.mp h1, Nat.even_iff.mp h2]
    · rw [Nat.odd_iff.mp h1, Nat.odd_iff.mp (h.mp h1)]
  have hmod : (side1deg side (roddE P)) % 2 =
      (∑ w ∈ univ.filter (fun w => side w = true), rldeg P (RVx.out w)) % 2 := by
    unfold side1deg
    rw [Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_nat_mod]
    congr 1
    exact Finset.sum_congr rfl (fun w _ => hw w)
  rw [Nat.odd_iff, Nat.odd_iff, hmod]

/-- Checks of a list of region vertices. -/
def isChk : RVx V W → Bool
  | RVx.chk _ => true
  | RVx.out _ => false

/-- The check of a region vertex, if it is one. -/
def getChk : RVx V W → Option V
  | RVx.chk v => some v
  | RVx.out _ => none

theorem map_filterMap_getChk : ∀ l : List (RVx V W), (∀ x ∈ l, isChk x = true) →
    (l.filterMap getChk).map RVx.chk = l
  | [], _ => rfl
  | x :: l, h => by
    cases x with
    | chk v =>
      simp only [List.filterMap_cons, getChk, List.map_cons]
      rw [map_filterMap_getChk l (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    | out w => exact absurd (h _ List.mem_cons_self) (by simp [isChk])

theorem mem_takeWhile_imp' {α : Type*} (p : α → Bool) : ∀ (t : List α) (x : α), x ∈ t.takeWhile p → p x = true
  | [], x, h => by simp at h
  | a :: t, x, h => by
    cases ha : p a
    · simp [List.takeWhile, ha] at h
    · simp only [List.takeWhile, ha, List.mem_cons] at h
      rcases h with rfl | h'
      · exact ha
      · exact mem_takeWhile_imp' p t x h'

theorem dropWhile_cons_not {α : Type*} (p : α → Bool) :
    ∀ (t : List α) (y : α) (r' : List α), t.dropWhile p = y :: r' → p y = false
  | [], y, r', h => by simp at h
  | a :: t, y, r', h => by
    cases ha : p a
    · simp only [List.dropWhile, ha, List.cons.injEq] at h
      rw [← h.1]
      exact ha
    · simp only [List.dropWhile, ha] at h
      exact dropWhile_cons_not p t y r' h

/-- **Cutting a path**: a simple path from a side-1 outer point to a side-2 outer point contains one whose interior
consists of checks only. -/
theorem cut_path {R : Finset (Sym2 (RVx V W))} (side : W → Bool)
    (hoo : ∀ w w' : W, ¬ (decGraph R).Adj (RVx.out w) (RVx.out w')) :
    ∀ (n : ℕ) (l : List (RVx V W)) (w1 w2 : W), l.length ≤ n → side w1 = true → side w2 = false →
      IsSPath (decGraph R) (RVx.out w1) (RVx.out w2) l →
      ∃ (a b : W) (v0 : V) (rest : List V), side a = true ∧ side b = false ∧
        IsSPath (decGraph R) (RVx.out a) (RVx.out b) (RVx.out a :: ((v0 :: rest).map RVx.chk ++ [RVx.out b])) := by
  intro n
  induction n with
  | zero =>
    intro l w1 w2 hl _ _ hp
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    exact absurd hp.head (by simp)
  | succ n ih =>
    intro l w1 w2 hl hs1 hs2 hp
    obtain ⟨hhead, hlast, hchain, hnd⟩ := hp
    -- l = out w1 :: t
    obtain ⟨t, rfl⟩ : ∃ t, l = RVx.out w1 :: t := by
      cases l with
      | nil => exact absurd hhead (by simp)
      | cons x t =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        exact ⟨t, by rw [hhead]⟩
    have ht : t ≠ [] := by
      rintro rfl
      simp only [List.getLast?_singleton, Option.some.injEq, RVx.out.injEq] at hlast
      subst hlast
      rw [hs1] at hs2
      exact absurd hs2 (by simp)
    have hlast' : t.getLast? = some (RVx.out w2) := by
      cases t with
      | nil => exact absurd rfl ht
      | cons y t' => rw [List.getLast?_cons_cons] at hlast; exact hlast
    -- the first outer point of t
    have htr : t = t.takeWhile isChk ++ t.dropWhile isChk := (List.takeWhile_append_dropWhile).symm
    have hcsC : ∀ x ∈ t.takeWhile isChk, isChk x = true := fun x hx => mem_takeWhile_imp' isChk t x hx
    obtain ⟨y, r', hyr⟩ : ∃ y r', t.dropWhile isChk = y :: r' := by
      cases hrr : t.dropWhile isChk with
      | nil =>
        exfalso
        rw [hrr, List.append_nil] at htr
        have hm : RVx.out w2 ∈ t := List.mem_of_getLast? hlast'
        rw [htr] at hm
        exact absurd (hcsC _ hm) (by simp [isChk])
      | cons y r' => exact ⟨y, r', rfl⟩
    have hy : isChk y = false := dropWhile_cons_not isChk t y r' hyr
    obtain ⟨wy, rfl⟩ : ∃ wy, y = RVx.out wy := by
      cases y with
      | chk v => exact absurd hy (by simp [isChk])
      | out w => exact ⟨w, rfl⟩
    set cs := t.takeWhile isChk with hcs
    have htr' : t = cs ++ RVx.out wy :: r' := by rw [htr, hyr]
    have hl : RVx.out w1 :: t = (RVx.out w1 :: cs ++ [RVx.out wy]) ++ r' := by
      rw [htr']; simp
    cases hsy : side wy with
    | false =>
      -- the prefix out w1 :: cs ++ [out wy]
      have hpre : (RVx.out w1 :: cs ++ [RVx.out wy]) <+: RVx.out w1 :: t := ⟨r', hl.symm⟩
      have hcsne : cs ≠ [] := by
        intro hc
        have hch := hchain.prefix hpre
        rw [hc] at hch
        simp only [List.nil_append, List.cons_append, List.isChain_cons_cons] at hch
        exact hoo w1 wy hch.1
      obtain ⟨v0, rest, hvr⟩ : ∃ v0 rest, cs.filterMap getChk = v0 :: rest := by
        cases hf : cs.filterMap getChk with
        | nil =>
          have := map_filterMap_getChk cs hcsC
          rw [hf] at this
          exact absurd this.symm hcsne
        | cons v0 rest => exact ⟨v0, rest, rfl⟩
      have hcseq : cs = (v0 :: rest).map RVx.chk := by
        rw [← hvr]; exact (map_filterMap_getChk cs hcsC).symm
      refine ⟨w1, wy, v0, rest, hs1, hsy, ?_⟩
      rw [← hcseq]
      refine ⟨by simp, ?_, ?_, ?_⟩
      · rw [← List.cons_append, List.getLast?_concat]
      · have := hchain.prefix hpre
        simpa using this
      · have := hnd.sublist hpre.sublist
        simpa using this
    | true =>
      -- restart from out wy
      have hsuf : (RVx.out wy :: r') <:+ RVx.out w1 :: t := by
        refine ⟨RVx.out w1 :: cs, ?_⟩
        rw [htr']; simp
      have hlen : (RVx.out wy :: r').length ≤ n := by
        have h2 : (RVx.out wy :: r').length < (RVx.out w1 :: t).length := by
          rw [htr']; simp
        omega
      have hlast2 : (RVx.out wy :: r').getLast? = some (RVx.out w2) := by
        rw [htr', List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hlast'
        exact hlast'
      exact ih (RVx.out wy :: r') wy w2 hlen hsy hs2
        ⟨by simp, hlast2, hchain.suffix hsuf, hnd.sublist hsuf.sublist⟩

end RDecoder

open RDecoder

theorem exists_phiMinFailR (Eg : Finset (Sym2 (RVx V W))) (side : W → Bool) (Φ : Sym2 (RVx V W) → ℤ)
    {E : Finset (Sym2 (RVx V W))} (h : ∃ C, IsMinCorrR Eg (rbd E) C ∧ FailsR side E C) :
    ∃ C, IsPhiMinFailR Eg side Φ E C := by
  classical
  set S := Eg.powerset.filter (fun C => IsMinCorrR Eg (rbd E) C ∧ FailsR side E C) with hS
  obtain ⟨C0, hC0⟩ := h
  have hne : S.Nonempty := ⟨C0, by simp only [hS, mem_filter, mem_powerset]; exact ⟨hC0.1.1, hC0⟩⟩
  obtain ⟨C, hCS, hmin⟩ := S.exists_min_image (fun C => ∑ e ∈ C, Φ e) hne
  simp only [hS, mem_filter, mem_powerset] at hCS
  refine ⟨C, hCS.2.1, hCS.2.2, fun C' hC' hf' => hmin C' ?_⟩
  simp only [hS, mem_filter, mem_powerset]
  exact ⟨hC'.1, hC', hf'⟩

/-- The failure path of a region code. -/
theorem failure_pathR {Eg E C : Finset (Sym2 (RVx V W))} (side : W → Bool) (hdiag : ∀ e ∈ Eg, ¬ e.IsDiag)
    (hoo : ∀ w w' : W, s(RVx.out w, RVx.out w') ∉ Eg) (hE : E ⊆ Eg) (hC : IsMinCorrR Eg (rbd E) C)
    (hf : FailsR side E C) :
    ∃ (w1 w2 : W) (v0 : V) (rest : List V), side w1 = true ∧ side w2 = false ∧
      IsSPath (decGraph (E ∆ C)) (RVx.out w1) (RVx.out w2)
        (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2])) := by
  classical
  set R := E ∆ C with hR
  have hRE : R ⊆ Eg := fun e he =>
    (Finset.mem_union.mp (Finset.symmDiff_subset_union he)).elim (fun h => hE h) (fun h => hC.1 h)
  have hdiagR : ∀ e ∈ R, ¬ e.IsDiag := fun e he => hdiag e (hRE he)
  have hooR : ∀ w w' : W, ¬ (decGraph R).Adj (RVx.out w) (RVx.out w') :=
    fun w w' h => hoo w w' (hRE h.2)
  -- every check has even degree in `R`
  have hchk : ∀ v : V, Even (vdeg R (RVx.chk v)) := by
    intro v
    rw [← Nat.not_odd_iff_even, hR, odd_vdeg_symmDiff, not_not]
    have := congrArg (fun s => v ∈ s) hC.2.1
    simp only [rbd, mem_filter, mem_univ, true_and] at this
    exact Iff.of_eq this.symm
  -- the side-1 degree sum is odd
  have hs1 : Odd (side1deg side R) := by
    rw [hR, odd_side1deg_symmDiff]
    intro h
    exact hf h.symm
  -- the vertices reachable from a side-1 outer point
  set pr : RVx V W → Prop := fun y => ∃ w, side w = true ∧ (decGraph R).Reachable (RVx.out w) y with hpr
  set A : Finset (RVx V W) := univ.filter pr with hA
  have hAcl : ∀ u u', (decGraph R).Adj u u' → (u ∈ A ↔ u' ∈ A) := by
    intro u u' hadj
    simp only [hA, mem_filter, mem_univ, true_and, hpr]
    constructor
    · rintro ⟨w, hw, hr⟩; exact ⟨w, hw, hr.trans hadj.reachable⟩
    · rintro ⟨w, hw, hr⟩; exact ⟨w, hw, hr.trans hadj.symm.reachable⟩
  have hev := even_sum_vdeg_closed hdiagR A hAcl
  -- split the sum over checks, side-1 and side-2 outer points
  have hsum : ∑ y ∈ A, vdeg R y = ∑ v, (if pr (RVx.chk v) then vdeg R (RVx.chk v) else 0) +
      (side1deg side R + ∑ w ∈ univ.filter (fun w => ¬ side w = true),
        (if pr (RVx.out w) then vdeg R (RVx.out w) else 0)) := by
    rw [hA, Finset.sum_filter, sum_rvx (fun y => if pr y then vdeg R y else 0)]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun w => side w = true)]
    congr 1
    unfold side1deg
    apply Finset.sum_congr rfl
    intro w hw
    have : pr (RVx.out w) := ⟨w, (mem_filter.mp hw).2, SimpleGraph.Reachable.refl _⟩
    simp only [this, if_true]
  have hevC : Even (∑ v, (if pr (RVx.chk v) then vdeg R (RVx.chk v) else 0)) := by
    apply even_sum_of_evenR
    intro v _
    split_ifs
    · exact hchk v
    · exact ⟨0, rfl⟩
  -- so some side-2 outer point is reachable from a side-1 outer point
  have hex2 : ∃ w2, side w2 = false ∧ pr (RVx.out w2) := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ w ∈ univ.filter (fun w => ¬ side w = true),
        (if pr (RVx.out w) then vdeg R (RVx.out w) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      have hw' : side w = false := by simpa using (mem_filter.mp hw).2
      rw [if_neg (hcon w hw')]
    rw [hsum, h0, add_zero, Nat.even_add] at hev
    exact (Nat.not_even_iff_odd.mpr hs1) (hev.mp hevC)
  obtain ⟨w2, hw2, hpr2⟩ := hex2
  obtain ⟨w1, hw1, hreach⟩ := hpr2
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hsp : IsSPath (decGraph R) (RVx.out w1) (RVx.out w2) p.support :=
    ⟨by rw [List.head?_eq_some_head (SimpleGraph.Walk.support_ne_nil p), SimpleGraph.Walk.head_support],
     by rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil p), SimpleGraph.Walk.getLast_support],
     p.isChain_adj_support, (SimpleGraph.Walk.isPath_def p).mp hp⟩
  exact cut_path side hooR p.support.length p.support w1 w2 le_rfl hw1 hw2 hsp

theorem half_weight_unifR {Eg C : Finset (Sym2 (RVx V W))} {A : Finset V} (hC : IsMinCorrR Eg A C)
    {γ E : Finset (Sym2 (RVx V W))} (hγ : γ ⊆ Eg) (hbd : rbd γ = ∅) (hsub : γ ⊆ E ∆ C) :
    #(γ \ E) ≤ #(γ ∩ E) := by
  obtain ⟨hCE, hCA, hmin⟩ := hC
  have hvalid : C ∆ γ ⊆ Eg := fun e he =>
    (Finset.mem_union.mp (Finset.symmDiff_subset_union he)).elim (fun h => hCE h) (fun h => hγ h)
  have hbdA : rbd (C ∆ γ) = A := by
    rw [rbd_symmDiff, hbd, ← Finset.bot_eq_empty, symmDiff_bot, hCA]
  have hle := hmin _ hvalid hbdA
  have h1 := card_symmDiff_add C γ
  have h2 : γ \ E = γ ∩ C := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨hg, hn⟩
      refine ⟨hg, ?_⟩
      rcases Finset.mem_symmDiff.mp (hsub hg) with h | h
      · exact absurd h.1 hn
      · exact h.1
    · rintro ⟨hg, hc⟩
      refine ⟨hg, fun he => ?_⟩
      rcases Finset.mem_symmDiff.mp (hsub hg) with h | h
      · exact h.2 hc
      · exact h.2 he
  have h3 : γ ∩ E = γ \ C := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨hg, he⟩
      refine ⟨hg, fun hc => ?_⟩
      rcases Finset.mem_symmDiff.mp (hsub hg) with h | h
      · exact h.2 hc
      · exact h.2 he
    · rintro ⟨hg, hc⟩
      refine ⟨hg, ?_⟩
      rcases Finset.mem_symmDiff.mp (hsub hg) with h | h
      · exact h.1
      · exact absurd h.1 hc
  have h4 := Finset.card_sdiff_add_card_inter γ C
  rw [Finset.inter_comm C γ] at h1
  rw [h2, h3]
  omega

/-- **The exchange lemma for region codes.** -/
theorem exchangeR {Eg : Finset (Sym2 (RVx V W))} {side : W → Bool} {Φ : Sym2 (RVx V W) → ℤ}
    {E C : Finset (Sym2 (RVx V W))} (hC : IsPhiMinFailR Eg side Φ E C) {X Y P : List (Sym2 (RVx V W))}
    (hXY : (X ++ Y).Nodup) (hX : ∀ e ∈ X, e ∈ C) (hY : ∀ e ∈ Y, e ∉ C) (hg : ∀ e ∈ X ++ Y ++ P, e ∈ Eg)
    (hXYout : ∀ e ∈ X ++ Y, ∀ w : W, RVx.out w ∉ e)
    (hpar : Even (∑ w ∈ univ.filter (fun w => side w = true), rldeg P (RVx.out w)))
    (hodd : roddD P = roddD (X ++ Y)) :
    X.length ≤ Y.length + P.length ∧
      (X.length = Y.length + P.length → P.Nodup → (X.map Φ).sum ≤ (Y.map Φ).sum + (P.map Φ).sum) := by
  classical
  obtain ⟨⟨hCE, hCA, hmin⟩, hfail, hphi⟩ := hC
  have hXn : X.Nodup := (List.nodup_append.mp hXY).1
  have hYn : Y.Nodup := (List.nodup_append.mp hXY).2.1
  have hσg : ∀ e ∈ (X ++ Y).toFinset, e ∈ Eg := fun e he =>
    hg e (List.mem_append_left _ (List.mem_toFinset.mp he))
  have hPg : ∀ e ∈ roddE P, e ∈ Eg := fun e he =>
    hg e (List.mem_append_right _ (List.mem_toFinset.mp (roddE_subset P he)))
  -- the new correction
  have hC'g : (C ∆ (X ++ Y).toFinset) ∆ roddE P ⊆ Eg := by
    intro e he
    rcases Finset.mem_union.mp (Finset.symmDiff_subset_union he) with h | h
    · rcases Finset.mem_union.mp (Finset.symmDiff_subset_union h) with h' | h'
      · exact hCE h'
      · exact hσg e h'
    · exact hPg e h
  have hbdσ : rbd (X ++ Y).toFinset = roddD (X ++ Y) := by
    rw [← roddE_of_nodup hXY, rbd_roddE]
  have hC'bd : rbd ((C ∆ (X ++ Y).toFinset) ∆ roddE P) = rbd E := by
    rw [rbd_symmDiff, rbd_symmDiff, hbdσ, rbd_roddE, hodd, symmDiff_assoc, symmDiff_self, symmDiff_bot, hCA]
  -- the class is unchanged
  have hσout : side1deg side (X ++ Y).toFinset = 0 :=
    side1deg_eq_zero side (fun e he w => hXYout e (List.mem_toFinset.mp he) w)
  have hcls : Odd (side1deg side ((C ∆ (X ++ Y).toFinset) ∆ roddE P)) ↔ Odd (side1deg side C) := by
    rw [odd_side1deg_symmDiff, odd_side1deg_symmDiff, hσout, odd_side1deg_roddE]
    have h1 : ¬ Odd (∑ w ∈ univ.filter (fun w => side w = true), rldeg P (RVx.out w)) :=
      Nat.not_odd_iff_even.mpr hpar
    have h0 : ¬ Odd 0 := by decide
    tauto
  -- sizes
  have hCσ : C ∩ (X ++ Y).toFinset = X.toFinset := by
    ext e
    simp only [Finset.mem_inter, List.mem_toFinset, List.mem_append]
    constructor
    · rintro ⟨hc, hx | hy⟩
      · exact hx
      · exact absurd hc (hY e hy)
    · intro hx
      exact ⟨hX e hx, Or.inl hx⟩
  have hcardC1 : #(C ∆ (X ++ Y).toFinset) + X.length = #C + Y.length := by
    have h := card_symmDiff_add C (X ++ Y).toFinset
    rw [hCσ, List.toFinset_card_of_nodup hXn, List.toFinset_card_of_nodup hXY, List.length_append] at h
    omega
  have hoddle : #(roddE P) ≤ P.length :=
    (Finset.card_le_card (roddE_subset P)).trans (List.toFinset_card_le P)
  have hC'le : #((C ∆ (X ++ Y).toFinset) ∆ roddE P) ≤ #(C ∆ (X ++ Y).toFinset) + #(roddE P) :=
    (Finset.card_le_card Finset.symmDiff_subset_union).trans (Finset.card_union_le _ _)
  have hle := hmin _ hC'g hC'bd
  refine ⟨by omega, ?_⟩
  intro heq hPn
  -- equality: the alternative is disjoint from `C ∆ σ`, and the new correction is a failing minimizer
  have hoddP : roddE P = P.toFinset := roddE_of_nodup hPn
  have hcardP : #P.toFinset = P.length := List.toFinset_card_of_nodup hPn
  have h5 := card_symmDiff_add (C ∆ (X ++ Y).toFinset) (roddE P)
  rw [hoddP, hcardP] at h5
  rw [hoddP] at hle
  have hint0 : #((C ∆ (X ++ Y).toFinset) ∩ P.toFinset) = 0 := by omega
  have hcardC' : #((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) = #C := by omega
  have hdisjP : Disjoint (C ∆ (X ++ Y).toFinset) P.toFinset :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hint0)
  have hC'eq : (C ∆ (X ++ Y).toFinset) ∆ P.toFinset = (C ∆ (X ++ Y).toFinset) ∪ P.toFinset :=
    rsymmDiff_eq_union hdisjP
  rw [hoddP] at hC'g hC'bd hcls
  have hminC' : IsMinCorrR Eg (rbd E) ((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) :=
    ⟨hC'g, hC'bd, fun C'' h1 h2 => by rw [hcardC']; exact hmin C'' h1 h2⟩
  have hfailC' : FailsR side E ((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) := by
    unfold FailsR at hfail ⊢
    rw [hcls]
    exact hfail
  have hle2 := hphi _ hminC' hfailC'
  -- `Φ` of the new correction
  have hC1eq : C ∆ (X ++ Y).toFinset = (C \ X.toFinset) ∪ Y.toFinset := by
    ext e
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, List.mem_append]
    constructor
    · rintro (⟨hc, hn⟩ | ⟨hxy, hc⟩)
      · left; exact ⟨hc, fun hx => hn (Or.inl hx)⟩
      · rcases hxy with hx | hy
        · exact absurd (hX e hx) hc
        · right; exact hy
    · rintro (⟨hc, hx⟩ | hy)
      · left; exact ⟨hc, fun h => h.elim hx (fun hy => hY e hy hc)⟩
      · right; exact ⟨Or.inr hy, hY e hy⟩
  have hXs : X.toFinset ⊆ C := fun e he => hX e (List.mem_toFinset.mp he)
  have hphiC1 : ∑ e ∈ C ∆ (X ++ Y).toFinset, Φ e = ∑ e ∈ C, Φ e - (X.map Φ).sum + (Y.map Φ).sum := by
    rw [hC1eq, Finset.sum_union (by
      rw [Finset.disjoint_left]
      intro e he hy
      exact hY e (List.mem_toFinset.mp hy) (Finset.mem_sdiff.mp he).1)]
    rw [Finset.sum_sdiff_eq_sub hXs, List.sum_toFinset _ hXn, List.sum_toFinset _ hYn]
  have hphiC' : ∑ e ∈ (C ∆ (X ++ Y).toFinset) ∆ P.toFinset, Φ e =
      ∑ e ∈ C ∆ (X ++ Y).toFinset, Φ e + (P.map Φ).sum := by
    rw [hC'eq, Finset.sum_union hdisjP, List.sum_toFinset _ hPn]
  rw [hphiC', hphiC1] at hle2
  linarith

/-- ML decoding is at least as good as any minimum-weight decoder. -/
theorem PfailMLR_le_PfailMWR (Eg : Finset (Sym2 (RVx V W))) (side : W → Bool) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : PfailMLR Eg side p ≤ PfailMWR Eg side p := by
  classical
  let dec : Finset V → Bool := fun s =>
    if h : ∃ C, IsMinCorrR Eg s C then decide (Odd (side1deg side (Classical.choose h))) else false
  have hle : PfailMLR Eg side p ≤ PfailDecR Eg side p dec := by
    unfold PfailMLR
    exact ciInf_le (Set.finite_range _).bddBelow dec
  refine le_trans hle (PrIID_mono Eg hp0 hp1 ?_)
  intro E hE hne
  have hex : ∃ C, IsMinCorrR Eg (rbd E) C := by
    have hne' : (Eg.powerset.filter (fun C => rbd C = rbd E)).Nonempty :=
      ⟨E, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hE, rfl⟩⟩
    obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image _ (fun C => #C) hne'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hC
    exact ⟨C, hC.1, hC.2, fun C' hC' hbd =>
      hmin C' (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC', hbd⟩)⟩
  refine ⟨Classical.choose hex, Classical.choose_spec hex, ?_⟩
  have hdec : dec (rbd E) = decide (Odd (side1deg side (Classical.choose hex))) := by
    simp [dec, hex]
  rw [hdec] at hne
  intro hiff
  exact hne (decide_eq_decide.mpr hiff)

end QEC
