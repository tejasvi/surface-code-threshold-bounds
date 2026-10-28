import QEC.Count.BoxSound
import QEC.Count.Counting
import QEC.Count.IID
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Order.Interval.Finset.Nat

/-!
# Assembly: the failure probability of the box code

If some minimum-weight correction fails, take a failing one `C` of least `Φ` (`exists_phiMinFail`) and a simple path
`γ` from `b1` to `b2` in `E ∆ C` (`failure_path`). Its E-edges `S = γ ∩ E` satisfy `|γ \ S| ≤ |S|`
(`half_weight_unif`), and its interior `v0, …, vL` (checks; `v0` on the face `x_a = 0`, `vL` on the face
`x_a = N a - 1`, so `L ≥ N a - 1`) has a legal labelled pattern (`box_not_excl`). By the union bound and
`PrIID_inter_eq`, `P_fail ≤ ∑ p^|S| (1 - p)^|γ \ S|`, and by the tilt (`tilt_unif`) each term is at most
`ω_E^|S| ω_C^|γ \ S|` with `ω_E = pX`, `ω_C = (1 - p)/X`. The map `(γ, S) ↦ (v0, labels of the two half-edges,
pattern)` is injective; the two half-edges contribute at most `(ω_E + ω_C)²`, and the patterns are counted by
`sum_legal_le`, summed over the lengths `L ≥ N a - 1`.
-/

namespace QEC

open Finset QECComp
open scoped symmDiff

namespace Assembly

/-! ## Edges of the box code -/

section BoxEdges

variable {n : ℕ} {N : Fin n → ℕ}

theorem l1B_comm (u v : BoxV n N) : l1B u v = l1B v u := by
  unfold l1B
  exact Finset.sum_congr rfl (fun i _ => by rw [← Int.natAbs_neg, neg_sub])

theorem mem_boxEdges_det_det {a : Fin n} {u v : BoxV n N} :
    s(Vx.det u, Vx.det v) ∈ boxEdges n N a ↔ l1B u v = 1 := by
  constructor
  · intro h
    simp only [boxEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Prod.exists] at h
    rcases h with (⟨u', v', h1, h2⟩ | ⟨w, -, hw⟩) | ⟨w, -, hw⟩
    · rcases Sym2.eq_iff.mp h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← Vx.det.inj e1, ← Vx.det.inj e2]
        exact h1
      · rw [← Vx.det.inj e1, ← Vx.det.inj e2, l1B_comm]
        exact h1
    · rcases Sym2.eq_iff.mp hw with ⟨-, e2⟩ | ⟨-, e2⟩ <;> exact absurd e2 (by simp)
    · rcases Sym2.eq_iff.mp hw with ⟨-, e2⟩ | ⟨-, e2⟩ <;> exact absurd e2 (by simp)
  · exact mem_boxEdges_of_l1B

theorem mem_boxEdges_det_b1 {a : Fin n} {u : BoxV n N} (h : s(Vx.det u, Vx.b1) ∈ boxEdges n N a) :
    (u a : ℕ) = 0 := by
  simp only [boxEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, Prod.exists] at h
  rcases h with (⟨u', v', -, h2⟩ | ⟨w, hw0, hw⟩) | ⟨w, -, hw⟩
  · rcases Sym2.eq_iff.mp h2 with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact absurd e2 (by simp)
    · exact absurd e1 (by simp)
  · rcases Sym2.eq_iff.mp hw with ⟨e1, -⟩ | ⟨e1, -⟩
    · rw [← Vx.det.inj e1]; exact hw0
    · exact absurd e1 (by simp)
  · rcases Sym2.eq_iff.mp hw with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact absurd e2 (by simp)
    · exact absurd e1 (by simp)

theorem mem_boxEdges_det_b2 {a : Fin n} {u : BoxV n N} (h : s(Vx.det u, Vx.b2) ∈ boxEdges n N a) :
    (u a : ℕ) + 1 = N a := by
  simp only [boxEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, Prod.exists] at h
  rcases h with (⟨u', v', -, h2⟩ | ⟨w, -, hw⟩) | ⟨w, hw0, hw⟩
  · rcases Sym2.eq_iff.mp h2 with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact absurd e2 (by simp)
    · exact absurd e1 (by simp)
  · rcases Sym2.eq_iff.mp hw with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact absurd e2 (by simp)
    · exact absurd e1 (by simp)
  · rcases Sym2.eq_iff.mp hw with ⟨e1, -⟩ | ⟨e1, -⟩
    · rw [← Vx.det.inj e1]; exact hw0
    · exact absurd e1 (by simp)

theorem b1b2_not_mem {a : Fin n} : s(Vx.b1, Vx.b2) ∉ boxEdges n N a := by
  intro h
  simp only [boxEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, Prod.exists] at h
  rcases h with (⟨u', v', -, h2⟩ | ⟨w, -, hw⟩) | ⟨w, -, hw⟩
  · rcases Sym2.eq_iff.mp h2 with ⟨e1, -⟩ | ⟨e1, -⟩ <;> exact absurd e1 (by simp)
  · rcases Sym2.eq_iff.mp hw with ⟨e1, -⟩ | ⟨e1, -⟩ <;> exact absurd e1 (by simp)
  · rcases Sym2.eq_iff.mp hw with ⟨e1, -⟩ | ⟨e1, -⟩ <;> exact absurd e1 (by simp)

theorem boxEdges_not_diag {a : Fin n} : ∀ e ∈ boxEdges n N a, ¬ e.IsDiag := by
  intro e h
  simp only [boxEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, Prod.exists] at h
  rcases h with (⟨u', v', h1, rfl⟩ | ⟨w, -, rfl⟩) | ⟨w, -, rfl⟩
  · rw [Sym2.mk_isDiag_iff, Vx.det.injEq]
    rintro rfl
    simp [l1B] at h1
  · simp
  · simp

end BoxEdges

/-! ## Simple paths from `b1` to `b2` -/

section Paths

/-- A list without `b1`, `b2` is a list of checks. -/
theorem exists_dets {V : Type*} : ∀ (t : List (Vx V)), (∀ x ∈ t, x ≠ Vx.b1 ∧ x ≠ Vx.b2) →
    ∃ vs : List V, t = vs.map Vx.det
  | [], _ => ⟨[], rfl⟩
  | x :: t, h => by
    obtain ⟨vs, hvs⟩ := exists_dets t (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases x with
    | det v => exact ⟨v :: vs, by simp [hvs]⟩
    | b1 => exact absurd rfl (h _ List.mem_cons_self).1
    | b2 => exact absurd rfl (h _ List.mem_cons_self).2

/-- A simple path from `b1` to `b2` (without a `b1`-`b2` edge) is `b1`, checks, `b2`. -/
theorem path_decomp {V : Type*} {G : SimpleGraph (Vx V)} {l : List (Vx V)} (hl : IsSPath G Vx.b1 Vx.b2 l)
    (hb12 : ¬ G.Adj Vx.b1 Vx.b2) :
    ∃ v0 : V, ∃ rest : List V, l = Vx.b1 :: ((v0 :: rest).map Vx.det ++ [Vx.b2]) := by
  obtain ⟨hh, hlast, hch, hnd⟩ := hl
  match l, hh, hlast, hch, hnd with
  | x :: t, hh, hlast, hch, hnd =>
    have hx : x = Vx.b1 := by simpa using hh
    subst hx
    have ht : t ≠ [] := by
      rintro rfl
      simp at hlast
    obtain ⟨t', y, rfl⟩ : ∃ t' y, t = t' ++ [y] := ⟨t.dropLast, t.getLast ht, (List.dropLast_append_getLast ht).symm⟩
    have hy : y = Vx.b2 := by
      rw [← List.cons_append, List.getLast?_append, List.getLast?_singleton] at hlast
      simpa using hlast
    subst hy
    have ht' : t' ≠ [] := by
      rintro rfl
      simp only [List.nil_append, List.isChain_cons_cons] at hch
      exact hb12 hch.1
    obtain ⟨vs, hvs⟩ := exists_dets t' (by
      intro z hz
      constructor
      · rintro rfl
        exact (List.nodup_cons.mp hnd).1 (List.mem_append_left _ hz)
      · rintro rfl
        have := (List.nodup_cons.mp hnd).2
        rw [List.nodup_append] at this
        exact this.2.2 _ hz _ (by simp) rfl)
    subst hvs
    match vs, ht' with
    | v0 :: rest, _ => exact ⟨v0, rest, rfl⟩

variable {n : ℕ} {N : Fin n → ℕ}

/-- A chain of checks in a subgraph of the box code is an adjacency chain. -/
theorem adjChain_of_isChain {a : Fin n} {R : Finset (Sym2 (Vx (BoxV n N)))} (hR : R ⊆ boxEdges n N a) :
    ∀ vs : List (BoxV n N), (vs.map Vx.det).IsChain (decGraph R).Adj → AdjChain vs
  | [], _ => trivial
  | [_], _ => trivial
  | u :: v :: rest, h => by
    simp only [List.map_cons, List.isChain_cons_cons] at h
    exact ⟨mem_boxEdges_det_det.mp (hR h.1.2), adjChain_of_isChain hR (v :: rest) h.2⟩

/-- The facts about a simple path from `b1` to `b2` in a subgraph of the box code. -/
theorem path_facts {a : Fin n} {R : Finset (Sym2 (Vx (BoxV n N)))} (hR : R ⊆ boxEdges n N a) {v0 : BoxV n N}
    {rest : List (BoxV n N)} (hl : IsSPath (decGraph R) Vx.b1 Vx.b2 (Vx.b1 :: ((v0 :: rest).map Vx.det ++ [Vx.b2]))) :
    AdjChain (v0 :: rest) ∧ (v0 :: rest).Nodup ∧ (v0 a : ℕ) = 0 ∧
      (((v0 :: rest).getLast (List.cons_ne_nil _ _)) a : ℕ) + 1 = N a := by
  obtain ⟨-, -, hch, hnd⟩ := hl
  have hch' := hch
  rw [List.map_cons, List.cons_append, List.isChain_cons_cons] at hch'
  obtain ⟨h01, hrest⟩ := hch'
  rw [← List.cons_append, ← List.map_cons, List.isChain_append] at hrest
  obtain ⟨hvs, -, hlast⟩ := hrest
  refine ⟨adjChain_of_isChain hR _ hvs, ?_, ?_, ?_⟩
  · have := (List.nodup_cons.mp hnd).2
    rw [List.nodup_append] at this
    exact List.Nodup.of_map _ this.1
  · have h := hR h01.2
    rw [Sym2.eq_swap] at h
    exact mem_boxEdges_det_b1 h
  · have hgl : ((v0 :: rest).map Vx.det).getLast? = some (Vx.det ((v0 :: rest).getLast (List.cons_ne_nil _ _))) := by
      rw [List.getLast?_eq_getLast (by simp), List.getLast_map]
    have := hlast _ hgl Vx.b2 (by simp)
    exact mem_boxEdges_det_b2 (hR this.2)

end Paths

/-! ## Weights of labelled paths -/

section Weights

theorem lwt_append_single {X : Type*} (f : Sym2 X → ℝ) (y : X) :
    ∀ (L : List X) (h : L ≠ []), lwt f (L ++ [y]) = lwt f L * f s(L.getLast h, y)
  | [], h => absurd rfl h
  | [x], _ => by simp
  | x :: z :: L, _ => by
    simp only [List.cons_append, lwt_cons_cons]
    rw [← List.cons_append, lwt_append_single f y (z :: L) (List.cons_ne_nil _ _), List.getLast_cons_cons]
    ring

theorem ledges_append_single {X : Type*} (y : X) :
    ∀ (L : List X) (h : L ≠ []), ledges (L ++ [y]) = ledges L ++ [s(L.getLast h, y)]
  | [], h => absurd rfl h
  | [x], _ => by simp
  | x :: z :: L, _ => by
    simp only [List.cons_append, ledges_cons_cons, List.cons.injEq, true_and]
    rw [← List.cons_append, ledges_append_single y (z :: L) (List.cons_ne_nil _ _), List.getLast_cons_cons]

variable {n : ℕ} {N : Fin n → ℕ}

/-- The weight of the edges between checks is the weight of the labelled pattern. -/
theorem lwt_patOf (ωE ωC : ℝ) (S : Finset (Sym2 (Vx (BoxV n N)))) :
    ∀ vs : List (BoxV n N),
      lwt (fun e => if e ∈ S then ωE else ωC) (vs.map Vx.det) = wtW ωE ωC (patOf S vs)
  | [] => by simp [patOf, wtW]
  | [_] => by simp [patOf, wtW]
  | u :: v :: rest => by
    simp only [List.map_cons, lwt_cons_cons, patOf, wtW, List.map_cons, List.prod_cons]
    rw [← List.map_cons, lwt_patOf ωE ωC S (v :: rest)]
    simp only [wtW, decide_not]
    by_cases h : s(Vx.det u, Vx.det v) ∈ S <;> simp [h]

end Weights

/-! ## Windows of the interior -/

section Windows

variable {n : ℕ} {N : Fin n → ℕ}

theorem patOf_drop (S : Finset (Sym2 (Vx (BoxV n N)))) :
    ∀ (vs : List (BoxV n N)) (i : ℕ), (patOf S vs).drop i = patOf S (vs.drop i)
  | [], _ => by simp [patOf]
  | [_], 0 => rfl
  | [_], _ + 1 => by simp [patOf]
  | _ :: _ :: _, 0 => rfl
  | u :: v :: rest, i + 1 => by
    simp only [patOf, List.drop_succ_cons]
    exact patOf_drop S (v :: rest) i

theorem patOf_take (S : Finset (Sym2 (Vx (BoxV n N)))) :
    ∀ (vs : List (BoxV n N)) (m : ℕ), (patOf S vs).take m = patOf S (vs.take (m + 1))
  | [], _ => by simp [patOf]
  | [_], m => by simp [patOf]
  | u :: v :: rest, 0 => by simp [patOf]
  | u :: v :: rest, m + 1 => by
    simp only [patOf, List.take_succ_cons]
    rw [patOf_take S (v :: rest) m]
    cases rest with
    | nil => simp [patOf]
    | cons x rest => simp [List.take_succ_cons, patOf]

theorem adjChain_drop : ∀ (vs : List (BoxV n N)) (i : ℕ), AdjChain vs → AdjChain (vs.drop i)
  | [], _, _ => by simp [AdjChain]
  | [_], 0, _ => trivial
  | [_], _ + 1, _ => by simp [AdjChain]
  | _ :: _ :: _, 0, h => h
  | u :: v :: rest, i + 1, h => adjChain_drop (v :: rest) i h.2

theorem adjChain_take : ∀ (vs : List (BoxV n N)) (k : ℕ), AdjChain vs → AdjChain (vs.take k)
  | [], _, _ => by simp [AdjChain]
  | [_], 0, _ => trivial
  | [_], _ + 1, _ => by simp [AdjChain]
  | _ :: _ :: _, 0, _ => trivial
  | u :: v :: rest, 1, _ => trivial
  | u :: v :: rest, k + 2, h => by
    simp only [List.take_succ_cons]
    have := adjChain_take (v :: rest) (k + 1) h.2
    simp only [List.take_succ_cons] at this
    exact ⟨h.1, this⟩

theorem pairs_drop {α : Type*} : ∀ (vs : List α) (i : ℕ) {uv : α × α}, uv ∈ pairs (vs.drop i) → uv ∈ pairs vs
  | [], _, _, h => by simp [pairs] at h
  | [_], 0, _, h => h
  | [_], _ + 1, _, h => by simp [pairs] at h
  | _ :: _ :: _, 0, _, h => h
  | u :: v :: rest, i + 1, uv, h => by
    simp only [List.drop_succ_cons] at h
    simp only [pairs]
    exact List.mem_cons_of_mem _ (pairs_drop (v :: rest) i h)

theorem pairs_take {α : Type*} : ∀ (vs : List α) (k : ℕ) {uv : α × α}, uv ∈ pairs (vs.take k) → uv ∈ pairs vs
  | [], _, _, h => by simp [pairs] at h
  | [_], 0, _, h => by simp [pairs] at h
  | [_], _ + 1, _, h => by simp [pairs] at h
  | _ :: _ :: _, 0, _, h => by simp [pairs] at h
  | u :: v :: rest, 1, _, h => by simp [pairs] at h
  | u :: v :: rest, k + 2, uv, h => by
    simp only [List.take_succ_cons] at h
    simp only [pairs, List.mem_cons] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · right
      have h' : uv ∈ pairs ((v :: rest).take (k + 1)) := by simpa [List.take_succ_cons] using h
      exact pairs_take (v :: rest) (k + 1) h'

/-- The interior pattern of the failure path is legal (no window excluded, self-avoiding). -/
theorem legal_interior {a : Fin n} {c : List ℤ} {K : ℕ} {E C : Finset (Sym2 (Vx (BoxV n N)))}
    (hC : IsPhiMinFail (boxEdges n N a) (phiBox c) E C) {S : Finset (Sym2 (Vx (BoxV n N)))} {v0 : BoxV n N}
    {rest : List (BoxV n N)} (hadj : AdjChain (v0 :: rest)) (hnd : (v0 :: rest).Nodup)
    (hS : ∀ uv ∈ pairs (v0 :: rest), (s(Vx.det uv.1, Vx.det uv.2) ∈ S ↔ s(Vx.det uv.1, Vx.det uv.2) ∉ C)) :
    Legal n c (K + 1) (patOf S (v0 :: rest)) := by
  refine ⟨?_, dirOK_patOf S _ hadj, ?_⟩
  · unfold SelfAv
    have h1 := walkPts_patOf S v0 rest hadj
    rw [walkPts_eq_map (length_pos v0)] at h1
    have h2 : ((v0 :: rest).map pos).Nodup := hnd.map pos_injective
    rw [← h1] at h2
    exact h2.of_map _
  · intro i m hm2 hmM him
    rw [length_patOf] at him
    rw [patOf_drop, patOf_take]
    have hL : (v0 :: rest).length = rest.length + 1 := rfl
    have hi : i < (v0 :: rest).length := by omega
    have hlen : 0 < (((v0 :: rest).drop i).take (m + 1)).length := by
      rw [List.length_take, List.length_drop]
      omega
    obtain ⟨v', rest', hws⟩ : ∃ v' rest', ((v0 :: rest).drop i).take (m + 1) = v' :: rest' := by
      cases h : ((v0 :: rest).drop i).take (m + 1) with
      | nil => rw [h] at hlen; simp at hlen
      | cons v' rest' => exact ⟨v', rest', rfl⟩
    rw [hws]
    apply box_not_excl hC S v' rest'
    · rw [← hws]
      exact adjChain_take _ _ (adjChain_drop _ _ hadj)
    · rw [← hws]
      exact (hnd.sublist (List.drop_sublist _ _)).sublist (List.take_sublist _ _)
    · intro uv huv
      rw [← hws] at huv
      exact hS uv (pairs_drop _ i (pairs_take _ (m + 1) huv))

end Windows

/-! ## The crossing length -/

section Crossing

variable {n : ℕ} {N : Fin n → ℕ}

theorem coord_le_of_adj {u v : BoxV n N} (h : l1B u v = 1) (i : Fin n) : (v i : ℕ) ≤ (u i : ℕ) + 1 := by
  have : Int.natAbs (((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)) ≤ l1B u v := by
    unfold l1B
    exact Finset.single_le_sum (f := fun j => Int.natAbs (((u j : ℕ) : ℤ) - ((v j : ℕ) : ℤ)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [h] at this
  omega

theorem coord_last_le (i : Fin n) : ∀ (v0 : BoxV n N) (rest : List (BoxV n N)), AdjChain (v0 :: rest) →
    (((v0 :: rest).getLast (List.cons_ne_nil _ _)) i : ℕ) ≤ (v0 i : ℕ) + rest.length
  | v0, [], _ => by simp
  | v0, v :: rest, h => by
    have := coord_last_le i v rest h.2
    have h1 := coord_le_of_adj h.1 i
    rw [List.getLast_cons_cons]
    simp only [List.length_cons]
    omega

end Crossing

/-! ## Recovering a labelled path from its interior pattern -/

section Recover

/-- The checks of a list of vertices, in order. -/
def getDets {V : Type*} : List (Vx V) → List V
  | [] => []
  | Vx.det v :: l => v :: getDets l
  | Vx.b1 :: l => getDets l
  | Vx.b2 :: l => getDets l

theorem getDets_map_det {V : Type*} : ∀ vs : List V, getDets (vs.map Vx.det) = vs
  | [] => rfl
  | v :: vs => by simp [getDets, getDets_map_det vs]

theorem getDets_append {V : Type*} : ∀ l l' : List (Vx V), getDets (l ++ l') = getDets l ++ getDets l'
  | [], _ => rfl
  | Vx.det v :: l, l' => by simp [getDets, getDets_append l l']
  | Vx.b1 :: l, l' => by simp [getDets, getDets_append l l']
  | Vx.b2 :: l, l' => by simp [getDets, getDets_append l l']

theorem getDets_path {V : Type*} (v0 : V) (rest : List V) :
    getDets (Vx.b1 :: ((v0 :: rest).map Vx.det ++ [Vx.b2])) = v0 :: rest := by
  simp only [getDets, getDets_append, getDets_map_det, List.append_nil]

variable {n : ℕ} {N : Fin n → ℕ}

theorem patOf_eq_labels {S S' : Finset (Sym2 (Vx (BoxV n N)))} : ∀ vs : List (BoxV n N),
    patOf S vs = patOf S' vs → ∀ e ∈ ledges (vs.map Vx.det), (e ∈ S ↔ e ∈ S')
  | [], _, e, he => by simp at he
  | [_], _, e, he => by simp at he
  | u :: v :: rest, h, e, he => by
    simp only [patOf, List.cons.injEq, Prod.mk.injEq] at h
    simp only [List.map_cons, ledges_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · have h2 := h.1.2
      by_cases h1 : s(Vx.det u, Vx.det v) ∈ S <;> by_cases h3 : s(Vx.det u, Vx.det v) ∈ S' <;> simp_all
    · exact patOf_eq_labels (v :: rest) h.2 e (by simpa using he)

theorem rest_eq_of_patOf {S S' : Finset (Sym2 (Vx (BoxV n N)))} {v0 : BoxV n N} {rest rest' : List (BoxV n N)}
    (h : AdjChain (v0 :: rest)) (h' : AdjChain (v0 :: rest'))
    (hp : patOf S (v0 :: rest) = patOf S' (v0 :: rest')) : rest = rest' := by
  have e1 := walkPts_patOf S v0 rest h
  have e2 := walkPts_patOf S' v0 rest' h'
  rw [hp, e2] at e1
  have := List.map_injective_iff.mpr pos_injective e1
  simpa using this.symm

/-- The weight of a labelled path: the two half-edges and the interior pattern. -/
theorem path_weight (ωE ωC : ℝ) {S : Finset (Sym2 (Vx (BoxV n N)))} {v0 : BoxV n N} {rest : List (BoxV n N)}
    (hnd : (Vx.b1 :: ((v0 :: rest).map Vx.det ++ [Vx.b2])).Nodup)
    (hS : S ⊆ pedges (Vx.b1 :: ((v0 :: rest).map Vx.det ++ [Vx.b2]))) :
    ωE ^ #S * ωC ^ #(pedges (Vx.b1 :: ((v0 :: rest).map Vx.det ++ [Vx.b2])) \ S) =
      (if decide (s(Vx.b1, Vx.det v0) ∉ S) then ωC else ωE) * wtW ωE ωC (patOf S (v0 :: rest)) *
        (if decide (s(Vx.det ((v0 :: rest).getLast (List.cons_ne_nil _ _)), Vx.b2) ∉ S) then ωC else ωE) := by
  classical
  set l := Vx.b1 :: ((v0 :: rest).map Vx.det ++ [Vx.b2]) with hl
  have e1 : ∏ e ∈ pedges l, (if e ∈ S then ωE else ωC) = ωE ^ #S * ωC ^ #(pedges l \ S) := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hS, ← Finset.sdiff_eq_filter]
  rw [← e1, prod_pedges _ hnd, hl]
  rw [List.map_cons, List.cons_append, lwt_cons_cons, ← List.cons_append, ← List.map_cons,
    lwt_append_single _ _ _ (by simp), List.getLast_map, lwt_patOf]
  have hF : ∀ e : Sym2 (Vx (BoxV n N)), (if e ∈ S then ωE else ωC) = (if decide (e ∉ S) then ωC else ωE) := by
    intro e
    by_cases h : e ∈ S <;> simp [h]
  rw [hF, hF]
  ring

end Recover

theorem mem_iff_of_decide_eq {α : Type*} {s s' : Finset α} {e : α} {d1 : Decidable (e ∉ s)}
    {d2 : Decidable (e ∉ s')} (h : @decide (e ∉ s) d1 = @decide (e ∉ s') d2) : (e ∈ s ↔ e ∈ s') := by
  rw [decide_eq_decide] at h
  exact not_iff_not.mp h

/-- A shifted geometric sum. -/
theorem geom_shift_le {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) {A B K : ℕ} (hAK : K ≤ A) :
    ∑ L ∈ Finset.Ico A B, lam ^ (L - K) ≤ lam ^ (A - K) / (1 - lam) := by
  rcases le_or_gt A B with hAB | hAB
  · have h := Finset.sum_Ico_add' (fun L => lam ^ (L - K)) (A - K) (B - K) K
    simp only [Nat.add_sub_cancel, Nat.sub_add_cancel hAK, Nat.sub_add_cancel (hAK.trans hAB)] at h
    rw [← h]
    exact geom_sum_Ico_le_of_lt_one h0 h1
  · rw [Finset.Ico_eq_empty_of_le hAB.le, Finset.sum_empty]
    exact div_nonneg (pow_nonneg h0 _) (by linarith)

end Assembly

open scoped Classical in
/-- **The failure probability of the box code** from a certificate (rows at the weights `pX`, `(1 - p)/X`). -/
theorem pfail_box_le (n : ℕ) (N : Fin n → ℕ) (a : Fin n) (c : List ℤ) (K : ℕ)
    {p X lam Hmin : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 ≤ X) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hHmin : 0 < Hmin) (IsSt : List (ℕ × Bool) → Prop) (H : List (ℕ × Bool) → ℝ)
    (hlen : ∀ s, IsSt s → s.length = K ∧ DirOK n s)
    (hpos : ∀ s, IsSt s → Hmin ≤ H s)
    (hstart : ∀ s, s.length = K → Legal n c (K + 1) s → IsSt s)
    (hclosed : ∀ s, IsSt s → ∀ x, Succ n c s x → IsSt (s ++ [x]).tail)
    (hrow : ∀ s, IsSt s → ∑ x ∈ (cands n).filter (Succ n c s),
      wtW (p * X) ((1 - p) / X) [x] * H (s ++ [x]).tail ≤ lam * H s)
    (hK : K + 1 ≤ N a) :
    PfailMW (boxEdges n N a) p ≤
      #(univ.filter (fun u : BoxV n N => (u a : ℕ) = 0)) * (p * X + (1 - p) / X) ^ 2 *
        ((∑ s ∈ (pats n K).filter IsSt, wtW (p * X) ((1 - p) / X) s * H s) / Hmin) *
          (lam ^ (N a - 1 - K) / (1 - lam)) := by
  classical
  have hX0 : 0 < X := by linarith
  have hE0 : 0 ≤ p * X := (mul_pos hp0 hX0).le
  have hC0 : 0 ≤ (1 - p) / X := div_nonneg (by linarith) hX0.le
  unfold PfailMW
  set ωE := p * X with hωE
  set ωC := (1 - p) / X with hωC
  set Eg := boxEdges n N a with hEg
  set S0 := (∑ s ∈ (pats n K).filter IsSt, wtW ωE ωC s * H s) / Hmin with hS0
  have hS0nn : 0 ≤ S0 := by
    apply div_nonneg _ hHmin.le
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (Counting.wtW_nonneg hE0 hC0 s) (hHmin.le.trans (hpos s (Finset.mem_filter.mp hs).2))
  set face := univ.filter (fun u : BoxV n N => (u a : ℕ) = 0) with hface
  have hgeo0 : 0 ≤ lam ^ (N a - 1 - K) / (1 - lam) := div_nonneg (pow_nonneg hlam0 _) (by linarith)
  -- the simple paths from `b1` to `b2`
  set spaths : Finset (List (Vx (BoxV n N))) :=
    ((univ : Finset {l : List (Vx (BoxV n N)) // l.Nodup}).map (Function.Embedding.subtype _)).filter
      (IsSPath (decGraph Eg) Vx.b1 Vx.b2) with hspaths
  have mem_spaths : ∀ l, l ∈ spaths ↔ IsSPath (decGraph Eg) Vx.b1 Vx.b2 l := by
    intro l
    simp only [hspaths, Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨⟨⟨l, h.nodup⟩, rfl⟩, h⟩
  -- the good labelled paths
  set I := (spaths ×ˢ Eg.powerset).filter (fun x : List (Vx (BoxV n N)) × Finset (Sym2 (Vx (BoxV n N))) =>
    x.2 ⊆ pedges x.1 ∧ #(pedges x.1 \ x.2) ≤ #x.2 ∧
      ∃ v0 rest, x.1 = Vx.b1 :: ((v0 :: rest).map Vx.det ++ [Vx.b2]) ∧ Legal n c (K + 1) (patOf x.2 (v0 :: rest)))
    with hI
  -- every failing error meets a good labelled path exactly in its E-edges
  have hincl : ∀ E ⊆ Eg, (∃ C, IsMinCorr Eg (bd E) C ∧ FailsB E C) → ∃ x ∈ I, E ∩ pedges x.1 = x.2 := by
    intro E hE hfail
    obtain ⟨C, hC⟩ := exists_phiMinFail Eg (phiBox c) hfail
    obtain ⟨l, hl⟩ := failure_path Assembly.boxEdges_not_diag hE hC.1 hC.2.1
    have hR : E ∆ C ⊆ Eg := fun e he =>
      (Finset.mem_union.mp (Finset.symmDiff_subset_union he)).elim (fun h => hE h) (fun h => hC.1.1 h)
    have hlEg : IsSPath (decGraph Eg) Vx.b1 Vx.b2 l :=
      ⟨hl.head, hl.last, hl.chain.imp (fun _ _ h => decGraph_mono hR h), hl.nodup⟩
    have hsubR : pedges l ⊆ E ∆ C := fun e he => ledges_subset_of_chain hl.chain e (List.mem_toFinset.mp he)
    have hsubEg : pedges l ⊆ Eg := hsubR.trans hR
    obtain ⟨v0, rest, hdec⟩ := Assembly.path_decomp hl (fun h => Assembly.b1b2_not_mem (hR h.2))
    refine ⟨(l, E ∩ pedges l), ?_, rfl⟩
    rw [hI, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, mem_spaths]
    refine ⟨⟨hlEg, Finset.inter_subset_left.trans hE⟩, Finset.inter_subset_right, ?_, v0, rest, hdec, ?_⟩
    · have h := half_weight_unif hC.1 hsubEg (bd_pedges_path hlEg) hsubR
      have e1 : pedges l \ (E ∩ pedges l) = pedges l \ E := by
        ext e
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [e1, Finset.inter_comm]
      exact h
    · have hf := Assembly.path_facts hR (hdec ▸ hl)
      apply Assembly.legal_interior hC hf.1 hf.2.1
      intro uv huv
      have hmem : s(Vx.det uv.1, Vx.det uv.2) ∈ pedges l := by
        rw [hdec]
        apply List.mem_toFinset.mpr
        rw [List.map_cons, List.cons_append, ledges_cons_cons, ← List.cons_append, ← List.map_cons,
          Assembly.ledges_append_single _ _ (by simp), ledges_map_det]
        apply List.mem_cons_of_mem
        apply List.mem_append_left
        exact List.mem_map_of_mem (f := fun uv : BoxV n N × BoxV n N => s(Vx.det uv.1, Vx.det uv.2)) huv
      have h2 := hsubR hmem
      rw [Finset.mem_symmDiff] at h2
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hE', -⟩ hC'
        rcases h2 with ⟨-, h⟩ | ⟨-, h⟩
        · exact h hC'
        · exact h hE'
      · intro hC'
        rcases h2 with ⟨h, -⟩ | ⟨h, -⟩
        · exact ⟨h, hmem⟩
        · exact absurd h hC'
  -- the union bound
  have hunion : PrIID Eg p (fun E => ∃ C, IsMinCorr Eg (bd E) C ∧ FailsB E C) ≤
      ∑ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) :=
    le_trans (PrIID_mono Eg hp0.le hp1.le hincl) (PrIID_exists_le Eg hp0.le hp1.le I _)
  -- each term, tilted
  have hterm : ∀ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) ≤ ωE ^ #x.2 * ωC ^ #(pedges x.1 \ x.2) := by
    intro x hx
    rw [hI, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, mem_spaths] at hx
    obtain ⟨⟨hl, -⟩, hS, hhalf, -⟩ := hx
    have hsubEg : pedges x.1 ⊆ Eg := fun e he => ledges_subset_of_chain hl.chain e (List.mem_toFinset.mp he)
    rw [PrIID_inter_eq Eg p hsubEg hS]
    exact tilt_unif hp0.le hp1.le hX hhalf
  have hRHS0 : 0 ≤ (#face : ℝ) * (ωE + ωC) ^ 2 * S0 * (lam ^ (N a - 1 - K) / (1 - lam)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hS0nn) hgeo0
  rcases Finset.eq_empty_or_nonempty I with hI0 | ⟨x0, hx0⟩
  · calc PrIID Eg p (fun E => ∃ C, IsMinCorr Eg (bd E) C ∧ FailsB E C)
        ≤ ∑ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) := hunion
      _ = 0 := by rw [hI0, Finset.sum_empty]
      _ ≤ _ := hRHS0
  -- a check, to define the injection
  obtain ⟨vstar, -, -⟩ : ∃ v0 : BoxV n N, ∃ rest : List (BoxV n N),
      x0.1 = Vx.b1 :: ((v0 :: rest).map Vx.det ++ [Vx.b2]) := by
    rw [hI, Finset.mem_filter] at hx0
    obtain ⟨-, -, -, v0, rest, h, -⟩ := hx0
    exact ⟨v0, rest, h⟩
  -- the injection into (first check, labels of the two half-edges, interior pattern)
  set f : List (Vx (BoxV n N)) × Finset (Sym2 (Vx (BoxV n N))) → BoxV n N × Bool × Bool × List (ℕ × Bool) :=
    fun x => ((Assembly.getDets x.1).headD vstar,
      decide (s(Vx.b1, Vx.det ((Assembly.getDets x.1).headD vstar)) ∉ x.2),
      decide (s(Vx.det ((Assembly.getDets x.1).getLastD vstar), Vx.b2) ∉ x.2),
      patOf x.2 (Assembly.getDets x.1)) with hf
  set g : BoxV n N × Bool × Bool × List (ℕ × Bool) → ℝ :=
    fun y => (if y.2.1 then ωC else ωE) * wtW ωE ωC y.2.2.2 * (if y.2.2.1 then ωC else ωE) with hg
  set Pset := (Finset.Ico (N a - 1) (Fintype.card (BoxV n N))).biUnion
    (fun L => (pats n L).filter (Legal n c (K + 1))) with hPset
  set J := face ×ˢ ((univ : Finset Bool) ×ˢ ((univ : Finset Bool) ×ˢ Pset)) with hJ
  have hfx : ∀ x ∈ I, ∃ v0 rest, x.1 = Vx.b1 :: ((v0 :: rest).map Vx.det ++ [Vx.b2]) ∧
      f x = (v0, decide (s(Vx.b1, Vx.det v0) ∉ x.2),
        decide (s(Vx.det ((v0 :: rest).getLast (List.cons_ne_nil _ _)), Vx.b2) ∉ x.2), patOf x.2 (v0 :: rest)) ∧
      AdjChain (v0 :: rest) ∧ (v0 :: rest).Nodup ∧ (v0 a : ℕ) = 0 ∧
      (((v0 :: rest).getLast (List.cons_ne_nil _ _)) a : ℕ) + 1 = N a ∧ Legal n c (K + 1) (patOf x.2 (v0 :: rest)) ∧
      x.2 ⊆ pedges x.1 ∧ x.1.Nodup := by
    intro x hx
    rw [hI, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, mem_spaths] at hx
    obtain ⟨⟨hl, -⟩, hS, -, v0, rest, hdec, hleg⟩ := hx
    have hpf := Assembly.path_facts (Finset.Subset.refl Eg) (hdec ▸ hl)
    refine ⟨v0, rest, hdec, ?_, hpf.1, hpf.2.1, hpf.2.2.1, hpf.2.2.2, hleg, hS, hl.nodup⟩
    simp only [hf, hdec, Assembly.getDets_path, List.headD_cons, List.getLastD_eq_getLast?,
      List.getLast?_eq_getLast (List.cons_ne_nil v0 rest), Option.getD_some]
  have hmaps : I.image f ⊆ J := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v0, rest, -, hfx1, hadj, hnd, h0, hlast, hleg, -, -⟩ := hfx x hx
    rw [hfx1, hJ]
    simp only [Finset.mem_product, Finset.mem_univ, true_and, hface, Finset.mem_filter]
    refine ⟨h0, ?_⟩
    rw [hPset, Finset.mem_biUnion]
    refine ⟨rest.length, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      have hc := Assembly.coord_last_le a v0 rest hadj
      have hcard := hnd.length_le_card
      simp only [List.length_cons] at hcard
      omega
    · rw [Finset.mem_filter, mem_pats, length_patOf]
      exact ⟨⟨by simp, dirOK_patOf _ _ hadj⟩, hleg⟩
  have hinj : Set.InjOn f I := by
    intro x hx x' hx' hxx
    obtain ⟨v0, rest, hdec, hfx1, hadj, -, -, -, -, hS, -⟩ := hfx x hx
    obtain ⟨v0', rest', hdec', hfx1', hadj', -, -, -, -, hS', -⟩ := hfx x' hx'
    rw [hfx1, hfx1'] at hxx
    simp only [Prod.mk.injEq] at hxx
    obtain ⟨rfl, hl1, hl2, hp⟩ := hxx
    have hrest : rest = rest' := Assembly.rest_eq_of_patOf hadj hadj' hp
    subst hrest
    have hl : x.1 = x'.1 := by rw [hdec, hdec']
    have hSS : x.2 = x'.2 := by
      ext e
      by_cases he : e ∈ pedges x.1
      · rw [hdec] at he
        have he' := List.mem_toFinset.mp he
        rw [List.map_cons, List.cons_append, ledges_cons_cons, ← List.cons_append, ← List.map_cons,
          Assembly.ledges_append_single _ _ (by simp), List.mem_cons, List.mem_append, List.mem_singleton,
          List.getLast_map] at he'
        rcases he' with rfl | he' | rfl
        · exact Assembly.mem_iff_of_decide_eq hl1
        · exact Assembly.patOf_eq_labels _ hp e he'
        · exact Assembly.mem_iff_of_decide_eq hl2
      · constructor
        · intro h
          exact absurd (hS h) he
        · intro h
          rw [hl] at he
          exact absurd (hS' h) he
    exact Prod.ext hl hSS
  have hwt : ∀ x ∈ I, ωE ^ #x.2 * ωC ^ #(pedges x.1 \ x.2) = g (f x) := by
    intro x hx
    obtain ⟨v0, rest, hdec, hfx1, -, -, -, -, -, hS, hnd⟩ := hfx x hx
    rw [hfx1, hg]
    simp only
    rw [hdec] at hS hnd ⊢
    exact Assembly.path_weight ωE ωC hnd hS
  have hg0 : ∀ y ∈ J, y ∉ I.image f → 0 ≤ g y := by
    intro y _ _
    simp only [hg]
    apply mul_nonneg (mul_nonneg _ (Counting.wtW_nonneg hE0 hC0 _))
    · split_ifs
      · exact hC0
      · exact hE0
    · split_ifs
      · exact hC0
      · exact hE0
  have hsum1 : ∑ x ∈ I, ωE ^ #x.2 * ωC ^ #(pedges x.1 \ x.2) ≤ ∑ y ∈ J, g y :=
    Finset.sum_le_sum_of_injOn f hinj hmaps (fun x hx => le_of_eq (hwt x hx)) hg0
  -- the sum over the target
  set Wsum := ∑ w ∈ Pset, wtW ωE ωC w with hWsum
  have hJsum : ∑ y ∈ J, g y = #face * ((ωE + ωC) ^ 2 * Wsum) := by
    have hinner : ∀ l1 l2 : Bool, ∑ w ∈ Pset, (if l1 then ωC else ωE) * wtW ωE ωC w * (if l2 then ωC else ωE) =
        (if l1 then ωC else ωE) * Wsum * (if l2 then ωC else ωE) := by
      intro l1 l2
      rw [hWsum, Finset.mul_sum, Finset.sum_mul]
    rw [hJ, Finset.sum_product]
    have hconst : ∀ v ∈ face, ∑ z ∈ (univ : Finset Bool) ×ˢ ((univ : Finset Bool) ×ˢ Pset), g (v, z) =
        (ωE + ωC) ^ 2 * Wsum := by
      intro v _
      rw [Finset.sum_product]
      simp only [hg]
      simp only [Finset.sum_product, hinner, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
      ring
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  -- the patterns, by length
  have hPsum : Wsum ≤ S0 * (lam ^ (N a - 1 - K) / (1 - lam)) := by
    rw [hWsum, hPset, Finset.sum_biUnion]
    · calc ∑ L ∈ Finset.Ico (N a - 1) (Fintype.card (BoxV n N)),
            ∑ w ∈ (pats n L).filter (Legal n c (K + 1)), wtW ωE ωC w
          ≤ ∑ L ∈ Finset.Ico (N a - 1) (Fintype.card (BoxV n N)), lam ^ (L - K) * S0 := by
            apply Finset.sum_le_sum
            intro L hL
            rw [Finset.mem_Ico] at hL
            exact sum_legal_le n c K hE0 hC0 hlam0 hHmin IsSt H hlen hpos hstart hclosed hrow L (by omega)
        _ = S0 * ∑ L ∈ Finset.Ico (N a - 1) (Fintype.card (BoxV n N)), lam ^ (L - K) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun L _ => by ring)
        _ ≤ S0 * (lam ^ (N a - 1 - K) / (1 - lam)) :=
            mul_le_mul_of_nonneg_left (Assembly.geom_shift_le hlam0 hlam1 (by omega)) hS0nn
    · intro L _ L' _ hLL'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro w hw hw'
      rw [Finset.mem_filter, mem_pats] at hw hw'
      exact hLL' (hw.1.1.symm.trans hw'.1.1)
  calc PrIID Eg p (fun E => ∃ C, IsMinCorr Eg (bd E) C ∧ FailsB E C)
      ≤ ∑ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) := hunion
    _ ≤ ∑ x ∈ I, ωE ^ #x.2 * ωC ^ #(pedges x.1 \ x.2) := Finset.sum_le_sum hterm
    _ ≤ ∑ y ∈ J, g y := hsum1
    _ = #face * ((ωE + ωC) ^ 2 * Wsum) := hJsum
    _ ≤ #face * ((ωE + ωC) ^ 2 * (S0 * (lam ^ (N a - 1 - K) / (1 - lam)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPsum (sq_nonneg _)) (Nat.cast_nonneg _)
    _ = #face * (ωE + ωC) ^ 2 * S0 * (lam ^ (N a - 1 - K) / (1 - lam)) := by ring

end QEC
