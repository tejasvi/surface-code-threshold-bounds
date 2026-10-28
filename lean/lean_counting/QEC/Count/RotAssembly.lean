import QEC.Count.RotSound
import QEC.Count.CountingX
import QEC.Count.Assembly

/-!
# Assembly for the rotated code (SAFE rules)

As `Assembly.lean`, for the region code `rotEdges d`. If some minimum-weight correction fails, take a failing one `C`
of least `Φ` (`exists_phiMinFailR`) and the failure path (`failure_pathR`): a side-1 half-edge, checks `v0 … vL`, a
side-2 half-edge. `v0` has `U + V = 0` and `vL` has `U + V = d - 2`, so `L ≥ d - 2`. By `half_weight_unifR`, the union
bound, `PrIID_inter_eq` and `tilt_unif`, `P_fail ≤ ∑ ω`. The interior pattern is legal (`rot_not_exclS`, windows of at
most `K + 1 < d` edges). The map `(γ, S) ↦ (first half-edge, its label, pattern, last half-edge, its label)` is
injective. There are `#side1` first half-edges and at most two last half-edges per check (the check's neighbours
`(U + 1, V)`, `(U, V + 1)`), so the half-edges contribute at most `#side1 · 2 · (ω_E + ω_C)²`; the patterns are counted
by `sum_legal_leX`, summed over the lengths `L ≥ d - 2`.
-/

namespace QEC

open Finset QECComp
open scoped symmDiff

namespace RotAssembly

/-! ## Lattice geometry in two dimensions -/

theorem l1_two (a1 a2 b1 b2 : ℤ) : l1 [a1, a2] [b1, b2] = (a1 - b1).natAbs + (a2 - b2).natAbs := by
  simp [l1]

theorem l1_two_comm (a1 a2 b1 b2 : ℤ) : l1 [a1, a2] [b1, b2] = l1 [b1, b2] [a1, a2] := by
  rw [l1_two, l1_two, ← Int.natAbs_neg (a1 - b1), ← Int.natAbs_neg (a2 - b2), neg_sub, neg_sub]

theorem vecOf_two (dd : ℕ) (hd : dd < 4) :
    vecOf 2 dd = if dd = 0 then [1, 0] else if dd = 1 then [-1, 0] else if dd = 2 then [0, 1] else [0, -1] := by
  rcases (show dd = 0 ∨ dd = 1 ∨ dd = 2 ∨ dd = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

/-- Lattice neighbours differ by a unit vector. -/
theorem exists_dir {a1 a2 b1 b2 : ℤ} (h : l1 [a1, a2] [b1, b2] = 1) :
    ∃ dd < 4, [b1, b2] = addP [a1, a2] (vecOf 2 dd) := by
  rw [l1_two] at h
  have hc : (b1 = a1 + 1 ∧ b2 = a2) ∨ (b1 = a1 - 1 ∧ b2 = a2) ∨ (b1 = a1 ∧ b2 = a2 + 1) ∨
      (b1 = a1 ∧ b2 = a2 - 1) := by omega
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, by norm_num, by rw [vecOf_two 0 (by norm_num)]; simp [addP, h1, h2]⟩
  · exact ⟨1, by norm_num, by rw [vecOf_two 1 (by norm_num)]; simp [addP, h1, h2]; ring⟩
  · exact ⟨2, by norm_num, by rw [vecOf_two 2 (by norm_num)]; simp [addP, h1, h2]⟩
  · exact ⟨3, by norm_num, by rw [vecOf_two 3 (by norm_num)]; simp [addP, h1, h2]; ring⟩

variable {d : ℕ}

/-- The position of a check. -/
def cpos (v : RChk d) : List ℤ := [v.1.1, v.1.2]

theorem cpos_injective : Function.Injective (cpos (d := d)) := by
  intro u v h
  simp only [cpos, List.cons.injEq, and_true] at h
  exact Subtype.ext (Prod.ext h.1 h.2)

theorem adj_dir {u v : RChk d} (h : l1 [u.1.1, u.1.2] [v.1.1, v.1.2] = 1) :
    dirOfR u v < 4 ∧ [v.1.1, v.1.2] = addP [u.1.1, u.1.2] (vecOf 2 (dirOfR u v)) := by
  have hex := exists_dir h
  simp only [dirOfR, dif_pos hex]
  exact Classical.choose_spec hex

theorem walkPts_patOfR (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) :
    ∀ (v0 : RChk d) (rest : List (RChk d)), AdjChainR (v0 :: rest) →
      walkPts 2 (cpos v0) ((patOfR S (v0 :: rest)).map Prod.fst) = (v0 :: rest).map cpos
  | v0, [], _ => by simp [patOfR]
  | v0, v :: rest, h => by
    simp only [patOfR, List.map_cons, walkPts_cons, List.cons.injEq, true_and]
    have e := (adj_dir h.1).2
    simp only [cpos] at e ⊢
    rw [← e]
    exact walkPts_patOfR S v rest h.2

theorem length_patOfR (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) :
    ∀ vs : List (RChk d), (patOfR S vs).length = vs.length - 1
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by simp [patOfR, length_patOfR S (v :: rest)]

theorem dirOK_patOfR (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) :
    ∀ vs : List (RChk d), AdjChainR vs → DirOK 2 (patOfR S vs)
  | [], _ => by simp [patOfR, DirOK]
  | [_], _ => by simp [patOfR, DirOK]
  | u :: v :: rest, h => by
    intro x hx
    simp only [patOfR, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (adj_dir h.1).1
    · exact dirOK_patOfR S (v :: rest) h.2 x hx

theorem patOfR_drop (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) :
    ∀ (vs : List (RChk d)) (i : ℕ), (patOfR S vs).drop i = patOfR S (vs.drop i)
  | [], _ => by simp [patOfR]
  | [_], 0 => rfl
  | [_], _ + 1 => by simp [patOfR]
  | _ :: _ :: _, 0 => rfl
  | u :: v :: rest, i + 1 => by
    simp only [patOfR, List.drop_succ_cons]
    exact patOfR_drop S (v :: rest) i

theorem patOfR_take (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) :
    ∀ (vs : List (RChk d)) (m : ℕ), (patOfR S vs).take m = patOfR S (vs.take (m + 1))
  | [], _ => by simp [patOfR]
  | [_], m => by simp [patOfR]
  | u :: v :: rest, 0 => by simp [patOfR]
  | u :: v :: rest, m + 1 => by
    simp only [patOfR, List.take_succ_cons]
    rw [patOfR_take S (v :: rest) m]
    cases rest with
    | nil => simp [patOfR]
    | cons x rest => simp [List.take_succ_cons, patOfR]

theorem adjChainR_drop : ∀ (vs : List (RChk d)) (i : ℕ), AdjChainR vs → AdjChainR (vs.drop i)
  | [], _, _ => by simp [AdjChainR]
  | [_], 0, _ => trivial
  | [_], _ + 1, _ => by simp [AdjChainR]
  | _ :: _ :: _, 0, h => h
  | u :: v :: rest, i + 1, h => adjChainR_drop (v :: rest) i h.2

theorem adjChainR_take : ∀ (vs : List (RChk d)) (k : ℕ), AdjChainR vs → AdjChainR (vs.take k)
  | [], _, _ => by simp [AdjChainR]
  | [_], 0, _ => trivial
  | [_], _ + 1, _ => by simp [AdjChainR]
  | _ :: _ :: _, 0, _ => trivial
  | u :: v :: rest, 1, _ => trivial
  | u :: v :: rest, k + 2, h => by
    simp only [List.take_succ_cons]
    have := adjChainR_take (v :: rest) (k + 1) h.2
    simp only [List.take_succ_cons] at this
    exact ⟨h.1, this⟩

/-- The interior pattern of the failure path is legal. -/
theorem legal_interiorR {c : List ℤ} {K : ℕ} {E C : Finset (Sym2 (RVx (RChk d) (ROut d)))}
    (hC : IsPhiMinFailR (rotEdges d) rotSide (phiRot c) E C) {S : Finset (Sym2 (RVx (RChk d) (ROut d)))}
    {v0 : RChk d} {rest : List (RChk d)} (hadj : AdjChainR (v0 :: rest)) (hnd : (v0 :: rest).Nodup)
    (hS : ∀ uv ∈ pairs (v0 :: rest),
      (s(RVx.chk uv.1, RVx.chk uv.2) ∈ S ↔ s(RVx.chk uv.1, RVx.chk uv.2) ∉ C))
    (hKd : K + 1 < d) :
    LegalX 2 (ExclS 2 c) (K + 1) (patOfR S (v0 :: rest)) := by
  refine ⟨?_, dirOK_patOfR S _ hadj, ?_⟩
  · unfold SelfAv
    have h1 := walkPts_patOfR S v0 rest hadj
    rw [walkPts_eq_map (by simp [cpos] : (cpos v0).length = 2)] at h1
    have h2 : ((v0 :: rest).map cpos).Nodup := hnd.map cpos_injective
    rw [← h1] at h2
    exact h2.of_map _
  · intro i m hm2 hmM him
    rw [length_patOfR] at him
    rw [patOfR_drop, patOfR_take]
    have hL : (v0 :: rest).length = rest.length + 1 := rfl
    have hlen : 0 < (((v0 :: rest).drop i).take (m + 1)).length := by
      rw [List.length_take, List.length_drop]
      omega
    obtain ⟨v', rest', hws⟩ : ∃ v' rest', ((v0 :: rest).drop i).take (m + 1) = v' :: rest' := by
      cases h : ((v0 :: rest).drop i).take (m + 1) with
      | nil => rw [h] at hlen; simp at hlen
      | cons v' rest' => exact ⟨v', rest', rfl⟩
    have hlen' : rest'.length ≤ m := by
      have := congrArg List.length hws
      rw [List.length_take, List.length_cons] at this
      omega
    rw [hws]
    apply rot_not_exclS hC S v' rest'
    · rw [← hws]
      exact adjChainR_take _ _ (adjChainR_drop _ _ hadj)
    · rw [← hws]
      exact (hnd.sublist (List.drop_sublist _ _)).sublist (List.take_sublist _ _)
    · intro uv huv
      rw [← hws] at huv
      exact hS uv (Assembly.pairs_drop _ i (Assembly.pairs_take _ (m + 1) huv))
    · omega

/-! ## Edges of the rotated code -/

theorem rotAdj_comm (a b : RVx (RChk d) (ROut d)) : RotAdj a b ↔ RotAdj b a := by
  cases a <;> cases b <;> simp only [RotAdj, posR] <;> first | exact Iff.rfl | rw [l1_two_comm]

theorem mem_rotEdges {a b : RVx (RChk d) (ROut d)} : s(a, b) ∈ rotEdges d ↔ RotAdj a b := by
  simp only [rotEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Prod.exists]
  constructor
  · rintro ⟨x, y, hxy, he⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy
    · exact (rotAdj_comm _ _).mp hxy
  · intro h
    exact ⟨a, b, h, rfl⟩

theorem rotEdges_not_diag : ∀ e ∈ rotEdges d, ¬ e.IsDiag := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff]
    rintro rfl
    rw [mem_rotEdges] at he
    cases a <;> simp [RotAdj, posR, l1] at he

theorem out_out_not_mem (w w' : ROut d) : s(RVx.out w, RVx.out w') ∉ rotEdges d := by
  intro h
  rw [mem_rotEdges] at h
  simp [RotAdj] at h

theorem chk_cond (v : RChk d) :
    0 ≤ v.1.1 + v.1.2 ∧ v.1.1 + v.1.2 ≤ d - 2 ∧ -1 ≤ v.1.1 - v.1.2 ∧ v.1.1 - v.1.2 ≤ d - 1 := by
  have := v.2
  simp only [rotChk, Finset.mem_filter] at this
  exact this.2

theorem out_cond (w : ROut d) :
    (w.1.1 + w.1.2 = -1 ∨ w.1.1 + w.1.2 = d - 1) ∧ -1 ≤ w.1.1 - w.1.2 ∧ w.1.1 - w.1.2 ≤ d - 1 := by
  have := w.2
  simp only [rotOut, Finset.mem_filter] at this
  exact this.2

theorem l1_chk_chk {u v : RChk d} (h : s(RVx.chk u, RVx.chk v) ∈ rotEdges d) :
    l1 [u.1.1, u.1.2] [v.1.1, v.1.2] = 1 := by
  have := mem_rotEdges.mp h
  simpa [RotAdj, posR] using this

theorem l1_out_chk {w : ROut d} {v : RChk d} (h : s(RVx.out w, RVx.chk v) ∈ rotEdges d) :
    l1 [w.1.1, w.1.2] [v.1.1, v.1.2] = 1 := by
  have := mem_rotEdges.mp h
  simpa [RotAdj, posR] using this

/-! ## The crossing length -/

theorem sum_le_of_adj {u v : RChk d} (h : l1 [u.1.1, u.1.2] [v.1.1, v.1.2] = 1) :
    v.1.1 + v.1.2 ≤ u.1.1 + u.1.2 + 1 := by
  rw [l1_two] at h
  omega

theorem sum_last_le : ∀ (v0 : RChk d) (rest : List (RChk d)), AdjChainR (v0 :: rest) →
    ((v0 :: rest).getLast (List.cons_ne_nil _ _)).1.1 + ((v0 :: rest).getLast (List.cons_ne_nil _ _)).1.2 ≤
      v0.1.1 + v0.1.2 + rest.length
  | v0, [], _ => by simp
  | v0, v :: rest, h => by
    have := sum_last_le v rest h.2
    have h1 := sum_le_of_adj h.1
    rw [List.getLast_cons_cons]
    simp only [List.length_cons]
    push_cast
    omega

/-- The first check of the failure path, next to a side-1 outer point, has `U + V = 0`. -/
theorem sum_first {w : ROut d} {v : RChk d} (h : s(RVx.out w, RVx.chk v) ∈ rotEdges d) (hs : rotSide w = true) :
    v.1.1 + v.1.2 = 0 := by
  have h1 := l1_out_chk h
  rw [l1_two] at h1
  have hw : w.1.1 + w.1.2 = -1 := by simpa [rotSide] using hs
  have := chk_cond v
  omega

/-- The last check of the failure path, next to a side-2 outer point, has `U + V = d - 2`; the outer point is
`(U + 1, V)` or `(U, V + 1)`. -/
theorem last_facts {w : ROut d} {v : RChk d} (h : s(RVx.chk v, RVx.out w) ∈ rotEdges d) (hs : rotSide w = false)
    (hd : 2 ≤ d) :
    v.1.1 + v.1.2 = d - 2 ∧ (w.1 = (v.1.1 + 1, v.1.2) ∨ w.1 = (v.1.1, v.1.2 + 1)) := by
  rw [Sym2.eq_swap] at h
  have h1 := l1_out_chk h
  rw [l1_two] at h1
  have hw : w.1.1 + w.1.2 ≠ -1 := by simpa [rotSide] using hs
  have hw2 : w.1.1 + w.1.2 = d - 1 := by
    rcases (out_cond w).1 with h' | h'
    · exact absurd h' hw
    · exact h'
  have := chk_cond v
  refine ⟨by omega, ?_⟩
  have hc : (w.1.1 = v.1.1 + 1 ∧ w.1.2 = v.1.2) ∨ (w.1.1 = v.1.1 ∧ w.1.2 = v.1.2 + 1) := by omega
  rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl (Prod.ext e1 e2)
  · exact Or.inr (Prod.ext e1 e2)

/-! ## Simple paths from side 1 to side 2 -/

theorem adjChainR_of_isChain {R : Finset (Sym2 (RVx (RChk d) (ROut d)))} (hR : R ⊆ rotEdges d) :
    ∀ vs : List (RChk d), (vs.map RVx.chk).IsChain (decGraph R).Adj → AdjChainR vs
  | [], _ => trivial
  | [_], _ => trivial
  | u :: v :: rest, h => by
    simp only [List.map_cons, List.isChain_cons_cons] at h
    exact ⟨l1_chk_chk (hR h.1.2), adjChainR_of_isChain hR (v :: rest) h.2⟩

/-- The facts about a failure path in a subgraph of the rotated code. -/
theorem path_factsR {R : Finset (Sym2 (RVx (RChk d) (ROut d)))} (hR : R ⊆ rotEdges d) {w1 w2 : ROut d}
    {v0 : RChk d} {rest : List (RChk d)}
    (hl : IsSPath (decGraph R) (RVx.out w1) (RVx.out w2) (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2]))) :
    AdjChainR (v0 :: rest) ∧ (v0 :: rest).Nodup ∧ s(RVx.out w1, RVx.chk v0) ∈ R ∧
      s(RVx.chk ((v0 :: rest).getLast (List.cons_ne_nil _ _)), RVx.out w2) ∈ R := by
  obtain ⟨-, -, hch, hnd⟩ := hl
  have hch' := hch
  rw [List.map_cons, List.cons_append, List.isChain_cons_cons] at hch'
  obtain ⟨h01, hrest⟩ := hch'
  rw [← List.cons_append, ← List.map_cons, List.isChain_append] at hrest
  obtain ⟨hvs, -, hlast⟩ := hrest
  refine ⟨adjChainR_of_isChain hR _ hvs, ?_, h01.2, ?_⟩
  · have := (List.nodup_cons.mp hnd).2
    rw [List.nodup_append] at this
    exact List.Nodup.of_map _ this.1
  · have hgl : ((v0 :: rest).map (RVx.chk (W := ROut d))).getLast? =
        some (RVx.chk ((v0 :: rest).getLast (List.cons_ne_nil _ _))) := by
      rw [List.getLast?_eq_getLast (by simp), List.getLast_map]
    have := hlast _ hgl (RVx.out w2) (by simp)
    exact this.2

theorem ledges_map_chk {V W : Type*} : ∀ vs : List V,
    ledges (vs.map (RVx.chk (W := W))) = (pairs vs).map (fun uv => s(RVx.chk uv.1, RVx.chk uv.2))
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by
    simp only [List.map_cons, ledges_cons_cons, pairs, List.cons.injEq, true_and]
    exact ledges_map_chk (v :: rest)

/-- The edges of a failure path. -/
theorem ledges_pathR {V W : Type*} (w1 w2 : W) (v0 : V) (rest : List V) :
    ledges (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2])) =
      s(RVx.out w1, RVx.chk v0) :: (ledges ((v0 :: rest).map RVx.chk) ++
        [s(RVx.chk ((v0 :: rest).getLast (List.cons_ne_nil _ _)), RVx.out w2)]) := by
  rw [List.map_cons, List.cons_append, ledges_cons_cons, ← List.cons_append, ← List.map_cons,
    Assembly.ledges_append_single _ _ (by simp), List.getLast_map]

/-- No check has odd degree on a failure path. -/
theorem rbd_pathR {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] (w1 w2 : W) (v0 : V)
    (rest : List V) (hnd : (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2])).Nodup) :
    rbd (pedges (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2]))) = ∅ := by
  ext v
  simp only [rbd, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    Nat.not_odd_iff_even]
  have h := even_countP_ledges (RVx.chk v) hnd (List.cons_ne_nil _ _)
  have hh : (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2])).head? ≠ some (RVx.chk v) := by simp
  have hl : (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2])).getLast? ≠ some (RVx.chk v) := by
    rw [← List.cons_append, List.getLast?_append]
    simp
  rw [if_neg hh, if_neg hl, add_zero, add_zero] at h
  rwa [vdeg_pedges hnd]

/-! ## Recovering a labelled path from its parts -/

/-- The checks of a list of vertices, in order. -/
def getChksR {V W : Type*} : List (RVx V W) → List V
  | [] => []
  | RVx.chk v :: l => v :: getChksR l
  | RVx.out _ :: l => getChksR l

theorem getChksR_map_chk {V W : Type*} : ∀ vs : List V, getChksR (vs.map (RVx.chk (W := W))) = vs
  | [] => rfl
  | v :: vs => by simp [getChksR, getChksR_map_chk vs]

theorem getChksR_append {V W : Type*} : ∀ l l' : List (RVx V W), getChksR (l ++ l') = getChksR l ++ getChksR l'
  | [], _ => rfl
  | RVx.chk v :: l, l' => by simp [getChksR, getChksR_append l l']
  | RVx.out w :: l, l' => by simp [getChksR, getChksR_append l l']

theorem getChksR_path {V W : Type*} (w1 w2 : W) (v0 : V) (rest : List V) :
    getChksR (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2])) = v0 :: rest := by
  simp only [getChksR, getChksR_append, getChksR_map_chk, List.append_nil]

theorem getLastD_pathR {V W : Type*} (w1 w2 : W) (v0 : V) (rest : List V) (dflt : RVx V W) :
    (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2])).getLastD dflt = RVx.out w2 := by
  rw [List.getLastD_eq_getLast?, ← List.cons_append, List.getLast?_append]
  simp

theorem out_chk_eq {V W : Type*} {w w' : W} {v v' : V} (h : s(RVx.out w, RVx.chk v) = s(RVx.out w', RVx.chk v')) :
    w = w' ∧ v = v' := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨RVx.out.inj h1, RVx.chk.inj h2⟩
  · exact absurd h1 (by simp)

theorem patOfR_eq_labels {S S' : Finset (Sym2 (RVx (RChk d) (ROut d)))} : ∀ vs : List (RChk d),
    patOfR S vs = patOfR S' vs → ∀ e ∈ ledges (vs.map RVx.chk), (e ∈ S ↔ e ∈ S')
  | [], _, e, he => by simp at he
  | [_], _, e, he => by simp at he
  | u :: v :: rest, h, e, he => by
    simp only [patOfR, List.cons.injEq, Prod.mk.injEq] at h
    simp only [List.map_cons, ledges_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · have h2 := h.1.2
      by_cases h1 : s(RVx.chk u, RVx.chk v) ∈ S <;> by_cases h3 : s(RVx.chk u, RVx.chk v) ∈ S' <;> simp_all
    · exact patOfR_eq_labels (v :: rest) h.2 e (by simpa using he)

theorem rest_eq_of_patOfR {S S' : Finset (Sym2 (RVx (RChk d) (ROut d)))} {v0 : RChk d}
    {rest rest' : List (RChk d)} (h : AdjChainR (v0 :: rest)) (h' : AdjChainR (v0 :: rest'))
    (hp : patOfR S (v0 :: rest) = patOfR S' (v0 :: rest')) : rest = rest' := by
  have e1 := walkPts_patOfR S v0 rest h
  have e2 := walkPts_patOfR S' v0 rest' h'
  rw [hp, e2] at e1
  have := List.map_injective_iff.mpr cpos_injective e1
  simpa using this.symm

/-! ## Weights -/

theorem lwt_patOfR (ωE ωC : ℝ) (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) :
    ∀ vs : List (RChk d),
      lwt (fun e => if e ∈ S then ωE else ωC) (vs.map RVx.chk) = wtW ωE ωC (patOfR S vs)
  | [] => by simp [patOfR, wtW]
  | [_] => by simp [patOfR, wtW]
  | u :: v :: rest => by
    simp only [List.map_cons, lwt_cons_cons, patOfR, wtW, List.map_cons, List.prod_cons]
    rw [← List.map_cons, lwt_patOfR ωE ωC S (v :: rest)]
    simp only [wtW, decide_not]
    by_cases h : s(RVx.chk u, RVx.chk v) ∈ S <;> simp [h]

/-- The weight of a labelled failure path: the two half-edges and the interior pattern. -/
theorem path_weightR (ωE ωC : ℝ) {S : Finset (Sym2 (RVx (RChk d) (ROut d)))} {w1 w2 : ROut d} {v0 : RChk d}
    {rest : List (RChk d)} (hnd : (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2])).Nodup)
    (hS : S ⊆ pedges (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2]))) :
    ωE ^ #S * ωC ^ #(pedges (RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2])) \ S) =
      (if decide (s(RVx.out w1, RVx.chk v0) ∉ S) then ωC else ωE) * wtW ωE ωC (patOfR S (v0 :: rest)) *
        (if decide (s(RVx.chk ((v0 :: rest).getLast (List.cons_ne_nil _ _)), RVx.out w2) ∉ S) then ωC
          else ωE) := by
  classical
  set l := RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2]) with hl
  have e1 : ∏ e ∈ pedges l, (if e ∈ S then ωE else ωC) = ωE ^ #S * ωC ^ #(pedges l \ S) := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hS, ← Finset.sdiff_eq_filter]
  rw [← e1, prod_pedges _ hnd, hl]
  rw [List.map_cons, List.cons_append, lwt_cons_cons, ← List.cons_append, ← List.map_cons,
    Assembly.lwt_append_single _ _ _ (by simp), List.getLast_map, lwt_patOfR]
  have hF : ∀ e : Sym2 (RVx (RChk d) (ROut d)), (if e ∈ S then ωE else ωC) = (if decide (e ∉ S) then ωC else ωE) := by
    intro e
    by_cases h : e ∈ S <;> simp [h]
  rw [hF, hF]
  ring

end RotAssembly

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The failure probability of the rotated code** from a SAFE certificate (rows at the weights `pX`, `(1 - p)/X`). -/
theorem pfail_rot_le (d : ℕ) (c : List ℤ) (K : ℕ) {p X lam Hmin : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 ≤ X)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hHmin : 0 < Hmin) (IsSt : List (ℕ × Bool) → Prop)
    (H : List (ℕ × Bool) → ℝ)
    (hlen : ∀ s, IsSt s → s.length = K ∧ DirOK 2 s)
    (hpos : ∀ s, IsSt s → Hmin ≤ H s)
    (hstart : ∀ s, s.length = K → LegalX 2 (ExclS 2 c) (K + 1) s → IsSt s)
    (hclosed : ∀ s, IsSt s → ∀ x, SuccX 2 (ExclS 2 c) s x → IsSt (s ++ [x]).tail)
    (hrow : ∀ s, IsSt s → ∑ x ∈ (cands 2).filter (SuccX 2 (ExclS 2 c) s),
      wtW (p * X) ((1 - p) / X) [x] * H (s ++ [x]).tail ≤ lam * H s)
    (hK : K + 2 ≤ d) :
    PfailMWR (rotEdges d) rotSide p ≤
      #((rotEdges d).filter (fun e => ∃ w : ROut d, rotSide w = true ∧ RVx.out w ∈ e)) * 2 *
        (p * X + (1 - p) / X) ^ 2 *
          ((∑ s ∈ (pats 2 K).filter IsSt, wtW (p * X) ((1 - p) / X) s * H s) / Hmin) *
            (lam ^ (d - 2 - K) / (1 - lam)) := by
  classical
  have hX0 : 0 < X := by linarith
  have hE0 : 0 ≤ p * X := (mul_pos hp0 hX0).le
  have hC0 : 0 ≤ (1 - p) / X := div_nonneg (by linarith) hX0.le
  have hd2 : 2 ≤ d := by omega
  unfold PfailMWR
  set ωE := p * X with hωE
  set ωC := (1 - p) / X with hωC
  set Eg := rotEdges d with hEg
  set S0 := (∑ s ∈ (pats 2 K).filter IsSt, wtW ωE ωC s * H s) / Hmin with hS0
  have hS0nn : 0 ≤ S0 := by
    apply div_nonneg _ hHmin.le
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (Counting.wtW_nonneg hE0 hC0 s) (hHmin.le.trans (hpos s (Finset.mem_filter.mp hs).2))
  set S1 := (rotEdges d).filter (fun e => ∃ w : ROut d, rotSide w = true ∧ RVx.out w ∈ e) with hS1
  have hgeo0 : 0 ≤ lam ^ (d - 2 - K) / (1 - lam) := div_nonneg (pow_nonneg hlam0 _) (by linarith)
  -- the good labelled paths
  set NL := (univ : Finset {l : List (RVx (RChk d) (ROut d)) // l.Nodup}).map (Function.Embedding.subtype _)
    with hNL
  set I := (NL ×ˢ Eg.powerset).filter
    (fun x : List (RVx (RChk d) (ROut d)) × Finset (Sym2 (RVx (RChk d) (ROut d))) =>
      (∃ (w1 w2 : ROut d) (v0 : RChk d) (rest : List (RChk d)), rotSide w1 = true ∧ rotSide w2 = false ∧
        x.1 = RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2]) ∧
        IsSPath (decGraph Eg) (RVx.out w1) (RVx.out w2) x.1 ∧
        LegalX 2 (ExclS 2 c) (K + 1) (patOfR x.2 (v0 :: rest))) ∧
      x.2 ⊆ pedges x.1 ∧ #(pedges x.1 \ x.2) ≤ #x.2) with hI
  -- every failing error meets a good labelled path exactly in its E-edges
  have hincl : ∀ E ⊆ Eg, (∃ C, IsMinCorrR Eg (rbd E) C ∧ FailsR rotSide E C) → ∃ x ∈ I, E ∩ pedges x.1 = x.2 := by
    intro E hE hfail
    obtain ⟨C, hC⟩ := exists_phiMinFailR Eg rotSide (phiRot c) hfail
    obtain ⟨w1, w2, v0, rest, hs1, hs2, hl⟩ :=
      failure_pathR rotSide RotAssembly.rotEdges_not_diag RotAssembly.out_out_not_mem hE hC.1 hC.2.1
    have hR : E ∆ C ⊆ Eg := fun e he =>
      (Finset.mem_union.mp (Finset.symmDiff_subset_union he)).elim (fun h => hE h) (fun h => hC.1.1 h)
    set l := RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2]) with hl_def
    have hlEg : IsSPath (decGraph Eg) (RVx.out w1) (RVx.out w2) l :=
      ⟨hl.head, hl.last, hl.chain.imp (fun _ _ h => decGraph_mono hR h), hl.nodup⟩
    have hsubR : pedges l ⊆ E ∆ C := fun e he => ledges_subset_of_chain hl.chain e (List.mem_toFinset.mp he)
    have hsubEg : pedges l ⊆ Eg := hsubR.trans hR
    have hf := RotAssembly.path_factsR hR hl
    refine ⟨(l, E ∩ pedges l), ?_, rfl⟩
    rw [hI, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
    refine ⟨⟨Finset.mem_map.mpr ⟨⟨l, hl.nodup⟩, Finset.mem_univ _, rfl⟩, Finset.inter_subset_left.trans hE⟩,
      ⟨w1, w2, v0, rest, hs1, hs2, rfl, hlEg, ?_⟩, Finset.inter_subset_right, ?_⟩
    · apply RotAssembly.legal_interiorR hC hf.1 hf.2.1 _ (by omega)
      intro uv huv
      have hmem : s(RVx.chk uv.1, RVx.chk uv.2) ∈ pedges l := by
        rw [hl_def]
        apply List.mem_toFinset.mpr
        rw [RotAssembly.ledges_pathR, RotAssembly.ledges_map_chk]
        apply List.mem_cons_of_mem
        apply List.mem_append_left
        exact List.mem_map_of_mem (f := fun uv : RChk d × RChk d => s(RVx.chk uv.1, RVx.chk uv.2)) huv
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
    · have h := half_weight_unifR hC.1 hsubEg (RotAssembly.rbd_pathR w1 w2 v0 rest hl.nodup) hsubR
      have e1 : pedges l \ (E ∩ pedges l) = pedges l \ E := by
        ext e
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [e1, Finset.inter_comm]
      exact h
  -- the union bound
  have hunion : PrIID Eg p (fun E => ∃ C, IsMinCorrR Eg (rbd E) C ∧ FailsR rotSide E C) ≤
      ∑ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) :=
    le_trans (PrIID_mono Eg hp0.le hp1.le hincl) (PrIID_exists_le Eg hp0.le hp1.le I _)
  -- each term, tilted
  have hterm : ∀ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) ≤ ωE ^ #x.2 * ωC ^ #(pedges x.1 \ x.2) := by
    intro x hx
    rw [hI, Finset.mem_filter] at hx
    obtain ⟨-, ⟨w1, w2, v0, rest, -, -, -, hl, -⟩, hS, hhalf⟩ := hx
    have hsubEg : pedges x.1 ⊆ Eg := fun e he => ledges_subset_of_chain hl.chain e (List.mem_toFinset.mp he)
    rw [PrIID_inter_eq Eg p hsubEg hS]
    exact tilt_unif hp0.le hp1.le hX hhalf
  have hRHS0 : 0 ≤ (#S1 : ℝ) * 2 * (ωE + ωC) ^ 2 * S0 * (lam ^ (d - 2 - K) / (1 - lam)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num)) (sq_nonneg _)) hS0nn) hgeo0
  rcases Finset.eq_empty_or_nonempty I with hI0 | ⟨x0, hx0⟩
  · calc PrIID Eg p (fun E => ∃ C, IsMinCorrR Eg (rbd E) C ∧ FailsR rotSide E C)
        ≤ ∑ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) := hunion
      _ = 0 := by rw [hI0, Finset.sum_empty]
      _ ≤ _ := hRHS0
  -- a check, to define the injection
  obtain ⟨vstar⟩ : Nonempty (RChk d) := by
    rw [hI, Finset.mem_filter] at hx0
    obtain ⟨-, ⟨-, -, v0, -, -, -, -, -, -⟩, -, -⟩ := hx0
    exact ⟨v0⟩
  set dflt : RVx (RChk d) (ROut d) := RVx.chk vstar with hdflt
  -- the injection into (first half-edge, its label, interior pattern, direction of the last half-edge, its label)
  set f : List (RVx (RChk d) (ROut d)) × Finset (Sym2 (RVx (RChk d) (ROut d))) →
      Sym2 (RVx (RChk d) (ROut d)) × Bool × List (ℕ × Bool) × Bool × Bool :=
    fun x => (s(x.1.headD dflt, RVx.chk ((RotAssembly.getChksR x.1).headD vstar)),
      decide (s(x.1.headD dflt, RVx.chk ((RotAssembly.getChksR x.1).headD vstar)) ∉ x.2),
      patOfR x.2 (RotAssembly.getChksR x.1),
      decide (posR (x.1.getLastD dflt) = [((RotAssembly.getChksR x.1).getLastD vstar).1.1 + 1,
        ((RotAssembly.getChksR x.1).getLastD vstar).1.2]),
      decide (s(RVx.chk ((RotAssembly.getChksR x.1).getLastD vstar), x.1.getLastD dflt) ∉ x.2)) with hf
  set g : Sym2 (RVx (RChk d) (ROut d)) × Bool × List (ℕ × Bool) × Bool × Bool → ℝ :=
    fun y => (if y.2.1 then ωC else ωE) * wtW ωE ωC y.2.2.1 * (if y.2.2.2.2 then ωC else ωE) with hg
  set Pset := (Finset.Ico (d - 2) (Fintype.card (RChk d))).biUnion
    (fun L => (pats 2 L).filter (LegalX 2 (ExclS 2 c) (K + 1))) with hPset
  set J := S1 ×ˢ ((univ : Finset Bool) ×ˢ (Pset ×ˢ ((univ : Finset Bool) ×ˢ (univ : Finset Bool)))) with hJ
  have hfx : ∀ x ∈ I, ∃ (w1 w2 : ROut d) (v0 : RChk d) (rest : List (RChk d)),
      x.1 = RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2]) ∧
      f x = (s(RVx.out w1, RVx.chk v0), decide (s(RVx.out w1, RVx.chk v0) ∉ x.2), patOfR x.2 (v0 :: rest),
        decide (posR (RVx.out w2 : RVx (RChk d) (ROut d)) =
          [((v0 :: rest).getLast (List.cons_ne_nil _ _)).1.1 + 1, ((v0 :: rest).getLast (List.cons_ne_nil _ _)).1.2]),
        decide (s(RVx.chk ((v0 :: rest).getLast (List.cons_ne_nil _ _)), RVx.out w2) ∉ x.2)) ∧
      AdjChainR (v0 :: rest) ∧ (v0 :: rest).Nodup ∧ s(RVx.out w1, RVx.chk v0) ∈ Eg ∧
      s(RVx.chk ((v0 :: rest).getLast (List.cons_ne_nil _ _)), RVx.out w2) ∈ Eg ∧
      rotSide w1 = true ∧ rotSide w2 = false ∧ LegalX 2 (ExclS 2 c) (K + 1) (patOfR x.2 (v0 :: rest)) ∧
      x.2 ⊆ pedges x.1 ∧ x.1.Nodup := by
    intro x hx
    rw [hI, Finset.mem_filter] at hx
    obtain ⟨-, ⟨w1, w2, v0, rest, hs1, hs2, hdec, hl, hleg⟩, hS, -⟩ := hx
    have hpf := RotAssembly.path_factsR (Finset.Subset.refl Eg) (hdec ▸ hl)
    refine ⟨w1, w2, v0, rest, hdec, ?_, hpf.1, hpf.2.1, hpf.2.2.1, hpf.2.2.2, hs1, hs2, hleg, hS, hl.nodup⟩
    simp only [hf, hdec, RotAssembly.getChksR_path, List.headD_cons, RotAssembly.getLastD_pathR]
    simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getLast (List.cons_ne_nil v0 rest), Option.getD_some]
  have hmaps : I.image f ⊆ J := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w1, w2, v0, rest, -, hfx1, hadj, hnd, h01, hlast, hs1, hs2, hleg, -, -⟩ := hfx x hx
    rw [hfx1, hJ]
    simp only [Finset.mem_product, Finset.mem_univ, true_and, and_true]
    refine ⟨?_, ?_⟩
    · rw [hS1, Finset.mem_filter]
      exact ⟨h01, w1, hs1, Sym2.mem_mk_left _ _⟩
    · rw [hPset, Finset.mem_biUnion]
      refine ⟨rest.length, ?_, ?_⟩
      · rw [Finset.mem_Ico]
        have hc := RotAssembly.sum_last_le v0 rest hadj
        have h0 := RotAssembly.sum_first h01 hs1
        have hl2 := (RotAssembly.last_facts hlast hs2 hd2).1
        have hcard := hnd.length_le_card
        simp only [List.length_cons] at hcard
        constructor
        · omega
        · omega
      · rw [Finset.mem_filter, mem_pats, RotAssembly.length_patOfR]
        exact ⟨⟨by simp, RotAssembly.dirOK_patOfR _ _ hadj⟩, hleg⟩
  have hinj : Set.InjOn f I := by
    intro x hx x' hx' hxx
    obtain ⟨w1, w2, v0, rest, hdec, hfx1, hadj, -, -, hlast, -, hs2, -, hS, -⟩ := hfx x hx
    obtain ⟨w1', w2', v0', rest', hdec', hfx1', hadj', -, -, hlast', -, hs2', -, hS', -⟩ := hfx x' hx'
    rw [hfx1, hfx1'] at hxx
    simp only [Prod.mk.injEq] at hxx
    obtain ⟨h1, hl1, hp, hj, hl2⟩ := hxx
    obtain ⟨rfl, rfl⟩ := RotAssembly.out_chk_eq h1
    have hrest : rest = rest' := RotAssembly.rest_eq_of_patOfR hadj hadj' hp
    subst hrest
    have hw2 : w2 = w2' := by
      have f1 := (RotAssembly.last_facts hlast hs2 hd2).2
      have f2 := (RotAssembly.last_facts hlast' hs2' hd2).2
      set vl := (v0 :: rest).getLast (List.cons_ne_nil _ _) with hvl
      have key : ∀ w : ROut d, decide (posR (RVx.out w : RVx (RChk d) (ROut d)) = [vl.1.1 + 1, vl.1.2]) = true ↔
          w.1 = (vl.1.1 + 1, vl.1.2) := by
        intro w
        simp only [decide_eq_true_eq, posR, List.cons.injEq, and_true]
        constructor
        · rintro ⟨h1, h2⟩
          exact Prod.ext h1 h2
        · intro h
          rw [h]
          exact ⟨rfl, rfl⟩
      apply Subtype.ext
      rcases f1 with e1 | e1 <;> rcases f2 with e2 | e2
      · rw [e1, e2]
      · exfalso
        have h1 := (key w2).mpr e1
        rw [hj] at h1
        have h2 := (key w2').mp h1
        rw [e2] at h2
        simp only [Prod.mk.injEq] at h2
        omega
      · exfalso
        have h1 := (key w2').mpr e2
        rw [← hj] at h1
        have h2 := (key w2).mp h1
        rw [e1] at h2
        simp only [Prod.mk.injEq] at h2
        omega
      · rw [e1, e2]
    subst hw2
    have hl : x.1 = x'.1 := by rw [hdec, hdec']
    have hSS : x.2 = x'.2 := by
      ext e
      by_cases he : e ∈ pedges x.1
      · rw [hdec] at he
        have he' := List.mem_toFinset.mp he
        rw [RotAssembly.ledges_pathR, List.mem_cons, List.mem_append, List.mem_singleton] at he'
        rcases he' with rfl | he' | rfl
        · exact Assembly.mem_iff_of_decide_eq hl1
        · exact RotAssembly.patOfR_eq_labels _ hp e he'
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
    obtain ⟨w1, w2, v0, rest, hdec, hfx1, -, -, -, -, -, -, -, hS, hnd⟩ := hfx x hx
    rw [hfx1, hg]
    simp only
    rw [hdec] at hS hnd ⊢
    exact RotAssembly.path_weightR ωE ωC hnd hS
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
  have hJsum : ∑ y ∈ J, g y = #S1 * (2 * ((ωE + ωC) ^ 2 * Wsum)) := by
    rw [hJ, Finset.sum_product]
    have hconst : ∀ h1 ∈ S1,
        ∑ z ∈ (univ : Finset Bool) ×ˢ (Pset ×ˢ ((univ : Finset Bool) ×ˢ (univ : Finset Bool))), g (h1, z) =
          2 * ((ωE + ωC) ^ 2 * Wsum) := by
      intro h1 _
      simp only [hg, Finset.sum_product, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
      rw [hWsum]
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      ring
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  -- the patterns, by length
  have hPsum : Wsum ≤ S0 * (lam ^ (d - 2 - K) / (1 - lam)) := by
    rw [hWsum, hPset, Finset.sum_biUnion]
    · calc ∑ L ∈ Finset.Ico (d - 2) (Fintype.card (RChk d)),
            ∑ w ∈ (pats 2 L).filter (LegalX 2 (ExclS 2 c) (K + 1)), wtW ωE ωC w
          ≤ ∑ L ∈ Finset.Ico (d - 2) (Fintype.card (RChk d)), lam ^ (L - K) * S0 := by
            apply Finset.sum_le_sum
            intro L hL
            rw [Finset.mem_Ico] at hL
            exact sum_legal_leX 2 (ExclS 2 c) K hE0 hC0 hlam0 hHmin IsSt H hlen hpos hstart hclosed hrow L
              (by omega)
        _ = S0 * ∑ L ∈ Finset.Ico (d - 2) (Fintype.card (RChk d)), lam ^ (L - K) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun L _ => by ring)
        _ ≤ S0 * (lam ^ (d - 2 - K) / (1 - lam)) :=
            mul_le_mul_of_nonneg_left (Assembly.geom_shift_le hlam0 hlam1 (by omega)) hS0nn
    · intro L _ L' _ hLL'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro w hw hw'
      rw [Finset.mem_filter, mem_pats] at hw hw'
      exact hLL' (hw.1.1.symm.trans hw'.1.1)
  calc PrIID Eg p (fun E => ∃ C, IsMinCorrR Eg (rbd E) C ∧ FailsR rotSide E C)
      ≤ ∑ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) := hunion
    _ ≤ ∑ x ∈ I, ωE ^ #x.2 * ωC ^ #(pedges x.1 \ x.2) := Finset.sum_le_sum hterm
    _ ≤ ∑ y ∈ J, g y := hsum1
    _ = #S1 * (2 * ((ωE + ωC) ^ 2 * Wsum)) := hJsum
    _ ≤ #S1 * (2 * ((ωE + ωC) ^ 2 * (S0 * (lam ^ (d - 2 - K) / (1 - lam))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPsum (sq_nonneg _))
          (by norm_num)) (Nat.cast_nonneg _)
    _ = #S1 * 2 * (ωE + ωC) ^ 2 * S0 * (lam ^ (d - 2 - K) / (1 - lam)) := by ring

end QEC
