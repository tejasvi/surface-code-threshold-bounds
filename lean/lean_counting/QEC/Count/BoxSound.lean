import QEC.Count.BoxGeom
import QEC.Count.Decoder

/-!
# Soundness of the exclusions in the box (box domination)

Let `C` be a failing minimum-weight correction of least `Φ` (with `Φ = phiBox c`) for the box code, and `ws` a
self-avoiding path of checks whose edges are labelled by membership in `C`. Then no window `patOf S ws` is excluded:
a checked witness gives an alternative edge list of unit steps inside the bounding box of the window, hence inside
the box, and the exchange lemma (`exchange`) contradicts its size or `Φ` inequality. `Φ` comparisons are translation
invariant because they compare lists of equal total size.
-/

namespace QEC

open Finset QECComp

variable {n : ℕ} {N : Fin n → ℕ}

/-! ## Lists of points -/

/-- Consecutive pairs of a list. -/
def pairs {α : Type*} : List α → List (α × α)
  | u :: v :: rest => (u, v) :: pairs (v :: rest)
  | _ => []

theorem ledges_map_det : ∀ ws : List (BoxV n N),
    ledges (ws.map Vx.det) = (pairs ws).map (fun uv => s(Vx.det uv.1, Vx.det uv.2))
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by
    simp only [List.map_cons, ledges_cons_cons, pairs, List.cons.injEq, true_and]
    exact ledges_map_det (v :: rest)

theorem mem_pairs_infix {α : Type*} : ∀ {ws : List α} {u v : α}, (u, v) ∈ pairs ws → [u, v] <:+: ws
  | [], _, _, h => by simp [pairs] at h
  | [_], _, _, h => by simp [pairs] at h
  | a :: b :: rest, u, v, h => by
    simp only [pairs, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨[], rest, rfl⟩
    · exact (mem_pairs_infix h).trans (List.suffix_cons a _).isInfix

theorem adj_of_mem_pairs : ∀ {ws : List (BoxV n N)} {u v : BoxV n N}, AdjChain ws → (u, v) ∈ pairs ws → l1B u v = 1
  | [], _, _, _, h => by simp [pairs] at h
  | [_], _, _, _, h => by simp [pairs] at h
  | a :: b :: rest, u, v, hc, h => by
    simp only [pairs, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact hc.1
    · exact adj_of_mem_pairs hc.2 h

/-- `φ` is additive on points with the same number of coordinates. -/
theorem phiP_addP : ∀ (c a b : List ℤ), a.length = b.length → phiP c (addP a b) = phiP c a + phiP c b
  | [], _, _, _ => by simp [phiP]
  | _ :: _, [], [], _ => by simp [phiP, addP]
  | _ :: _, [], _ :: _, h => by simp at h
  | _ :: _, _ :: _, [], h => by simp at h
  | c :: cs, a :: as, b :: bs, h => by
    simp only [addP, phiP]
    rw [phiP_addP cs as bs (by simpa using h)]
    ring

/-- Coordinatewise difference. -/
def subP (a b : List ℤ) : List ℤ := List.zipWith (fun x y => x - y) a b

theorem addP_subP : ∀ (a b : List ℤ), a.length = b.length → addP b (subP a b) = a
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [subP, List.zipWith_cons_cons, addP, List.cons.injEq] at *
    exact ⟨by ring, addP_subP as bs (by simpa using h)⟩

theorem length_subP (a b : List ℤ) : (subP a b).length = min a.length b.length := by simp [subP]

/-! ## Translated edges -/

theorem edgesFrom_translate {o o' : List ℤ} (ho : o.length = n) (ho' : o'.length = n) :
    ∀ w : List (ℕ × Bool), edgesFrom n (addP o o') w =
      (edgesFrom n o' w).map (fun e => ((addP o e.1.1, addP o e.1.2), e.2))
  | [] => rfl
  | (d, l) :: w => by
    have ih := edgesFrom_translate (o' := addP o' (vecOf n d)) ho (by simp [ho']) w
    simp only [edgesFrom, List.map_cons, addP_assoc, ih]

theorem edgesFrom_patOf (S : Finset (Sym2 (Vx (BoxV n N)))) :
    ∀ (v0 : BoxV n N) (rest : List (BoxV n N)), AdjChain (v0 :: rest) →
      edgesFrom n (pos v0) (patOf S (v0 :: rest)) =
        (pairs (v0 :: rest)).map (fun uv => ((pos uv.1, pos uv.2), decide (s(Vx.det uv.1, Vx.det uv.2) ∉ S)))
  | v0, [], _ => rfl
  | v0, v :: rest, h => by
    simp only [patOf, edgesFrom, pairs, List.map_cons, List.cons.injEq]
    rw [← (dirOf_spec h.1).2]
    exact ⟨rfl, edgesFrom_patOf S v rest h.2⟩

theorem mem_edgesFrom_pts (n : ℕ) : ∀ (o : List ℤ) (w : List (ℕ × Bool)) (e : Edge × Bool),
    e ∈ edgesFrom n o w → e.1.1 ∈ walkPts n o (w.map Prod.fst) ∧ e.1.2 ∈ walkPts n o (w.map Prod.fst)
  | _, [], _, h => by simp [edgesFrom] at h
  | o, (d, l) :: w, e, h => by
    simp only [edgesFrom, List.mem_cons] at h
    simp only [List.map_cons, walkPts_cons, List.mem_cons]
    rcases h with rfl | h
    · refine ⟨Or.inl rfl, Or.inr ?_⟩
      cases w with
      | nil => simp
      | cons x w => simp
    · have := mem_edgesFrom_pts n _ w e h
      exact ⟨Or.inr this.1, Or.inr this.2⟩

/-! ## From relative points to checks -/

/-- The check at a position (`v0` if there is none). -/
noncomputable def toV (v0 : BoxV n N) (y : List ℤ) : BoxV n N :=
  open Classical in if h : ∃ u : BoxV n N, pos u = y then Classical.choose h else v0

theorem pos_toV {v0 : BoxV n N} {y : List ℤ} (h : ∃ u : BoxV n N, pos u = y) : pos (toV v0 y) = y := by
  simp only [toV, dif_pos h]
  exact Classical.choose_spec h

theorem toV_pos (v0 u : BoxV n N) : toV v0 (pos u) = u := pos_injective (pos_toV ⟨u, rfl⟩)

/-- The box edge of a relative edge, translated by the position of `v0`. -/
noncomputable def boxE (v0 : BoxV n N) (e : Edge) : Sym2 (Vx (BoxV n N)) :=
  s(Vx.det (toV v0 (addP (pos v0) e.1)), Vx.det (toV v0 (addP (pos v0) e.2)))

/-- The relative edges whose ends have `n` coordinates and are translated into the box. -/
def GoodE (v0 : BoxV n N) (L : List Edge) : Prop :=
  ∀ e ∈ L, e.1.length = n ∧ e.2.length = n ∧ (∃ u : BoxV n N, pos u = addP (pos v0) e.1) ∧
    (∃ u : BoxV n N, pos u = addP (pos v0) e.2)

theorem toV_eq_iff {v0 u : BoxV n N} {q : List ℤ} (hq : q.length = n) (hin : ∃ w : BoxV n N, pos w = addP (pos v0) q) :
    u = toV v0 (addP (pos v0) q) ↔ subP (pos u) (pos v0) = q := by
  constructor
  · intro h
    have h1 : pos u = addP (pos v0) q := by rw [h, pos_toV hin]
    apply addP_injOn (length_pos v0) (by simp [length_subP]) hq
    rw [addP_subP _ _ (by simp), h1]
  · intro h
    apply pos_injective
    rw [pos_toV hin, ← h, addP_subP _ _ (by simp)]

/-- Degrees of translated edges. -/
theorem ldeg_map_boxE (v0 : BoxV n N) {L : List Edge} (hL : GoodE v0 L) (u : BoxV n N) :
    ldeg (L.map (boxE v0)) (Vx.det u) = degC L (subP (pos u) (pos v0)) := by
  unfold ldeg degC
  rw [List.countP_map]
  apply List.countP_congr
  intro e he
  obtain ⟨h1, h2, h3, h4⟩ := hL e he
  simp only [Function.comp, boxE, Sym2.mem_iff, Vx.det.injEq, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  rw [toV_eq_iff h1 h3, toV_eq_iff h2 h4]
  constructor <;> rintro (h | h) <;> first | exact Or.inl h.symm | exact Or.inr h.symm

theorem boxE_inj_same {v0 : BoxV n N} {e f : Edge} (he : GoodE v0 [e]) (hf : GoodE v0 [f])
    (h : boxE v0 e = boxE v0 f) : sameE e f = true := by
  obtain ⟨e1, e2, e3, e4⟩ := he e (by simp)
  obtain ⟨f1, f2, f3, f4⟩ := hf f (by simp)
  have key : ∀ {a b : List ℤ}, a.length = n → b.length = n → (∃ w : BoxV n N, pos w = addP (pos v0) a) →
      (∃ w : BoxV n N, pos w = addP (pos v0) b) → toV v0 (addP (pos v0) a) = toV v0 (addP (pos v0) b) → a = b := by
    intro a b ha hb hia hib hab
    have := congrArg pos hab
    rw [pos_toV hia, pos_toV hib] at this
    exact addP_injOn (length_pos v0) ha hb this
  simp only [boxE, Sym2.eq_iff, Vx.det.injEq] at h
  simp only [sameE, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨key e1 f1 e3 f3 h1, key e2 f2 e4 f4 h2⟩
  · exact Or.inr ⟨key e1 f2 e3 f4 h1, key e2 f1 e4 f3 h2⟩

theorem nodup_map_boxE (v0 : BoxV n N) : ∀ {L : List Edge}, GoodE v0 L → nodupE L = true → (L.map (boxE v0)).Nodup
  | [], _, _ => List.nodup_nil
  | e :: L, hL, h => by
    simp only [nodupE, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_boxE v0 (fun f hf => hL f (List.mem_cons_of_mem _ hf)) h.2⟩
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hm
    have := boxE_inj_same (fun g hg => hL g (by simp at hg; simp [hg])) (fun g hg => hL g (by
      simp at hg; subst hg; exact List.mem_cons_of_mem _ hf)) hfe.symm
    rw [h.1 f hf] at this
    exact absurd this (by simp)

theorem phi_boxE (c : List ℤ) {v0 : BoxV n N} {e : Edge} (he : GoodE v0 [e]) :
    phiBox c (boxE v0 e) = phiP c e.1 + phiP c e.2 + 2 * phiP c (pos v0) := by
  obtain ⟨e1, e2, e3, e4⟩ := he e (by simp)
  simp only [boxE, phiBox, Sym2.lift_mk]
  rw [pos_toV e3, pos_toV e4, phiP_addP _ _ _ (by simp [e1]), phiP_addP _ _ _ (by simp [e2])]
  ring

theorem phi_map_boxE (c : List ℤ) (v0 : BoxV n N) : ∀ {L : List Edge}, GoodE v0 L →
    ((L.map (boxE v0)).map (phiBox c)).sum = phiE c L + 2 * L.length * phiP c (pos v0)
  | [], _ => by simp [phiE]
  | e :: L, hL => by
    simp only [List.map_cons, List.sum_cons, phiE, List.length_cons]
    rw [phi_boxE c (fun f hf => hL f (by simp at hf; simp [hf])),
      phi_map_boxE c v0 (fun f hf => hL f (List.mem_cons_of_mem _ hf))]
    push_cast
    ring

/-- A unit step between two translated points in the box is an edge of the box code. -/
theorem boxE_mem {a : Fin n} (v0 : BoxV n N) {x : List ℤ} {d : ℕ} (hd : d < 2 * n) (hx : x.length = n)
    (h1 : ∃ u : BoxV n N, pos u = addP (pos v0) x) (h2 : ∃ u : BoxV n N, pos u = addP (pos v0) (addP x (vecOf n d))) :
    boxE v0 (x, addP x (vecOf n d)) ∈ boxEdges n N a := by
  simp only [boxE, boxEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, Prod.exists]
  left; left
  refine ⟨toV v0 (addP (pos v0) x), toV v0 (addP (pos v0) (addP x (vecOf n d))), ?_, rfl⟩
  rw [l1B_eq_one_iff]
  refine ⟨d, hd, ?_⟩
  rw [pos_toV h1, pos_toV h2, addP_assoc]

/-- A point in the bounding box of points translated into the box is translated into the box. -/
theorem inBB_box {v0 : BoxV n N} {pts : List (List ℤ)} (hpts : ∀ p ∈ pts, p.length = n ∧
    ∃ u : BoxV n N, pos u = addP (pos v0) p) {x : List ℤ} (hx : inBB n pts x = true) :
    x.length = n ∧ ∃ u : BoxV n N, pos u = addP (pos v0) x := by
  simp only [inBB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, List.any_eq_true,
    decide_eq_true_eq] at hx
  obtain ⟨hlen, hcoord⟩ := hx
  refine ⟨hlen, exists_pos (by simp [hlen]) ?_⟩
  intro i
  obtain ⟨⟨p, hp, hpi⟩, ⟨q, hq, hqi⟩⟩ := hcoord i i.2
  obtain ⟨hpl, up, hup⟩ := hpts p hp
  obtain ⟨hql, uq, huq⟩ := hpts q hq
  rw [getD_addP _ _ _ (by simp) (by simp [hlen])]
  have e1 := congrArg (fun l => l.getD i 0) hup
  have e2 := congrArg (fun l => l.getD i 0) huq
  rw [getD_pos, getD_addP _ _ _ (by simp) (by simp [hpl])] at e1
  rw [getD_pos, getD_addP _ _ _ (by simp) (by simp [hql])] at e2
  have b1 := (up i).2
  have b2 := (uq i).2
  omega

theorem mem_boxEdges_of_l1B {a : Fin n} {u v : BoxV n N} (h : l1B u v = 1) :
    s(Vx.det u, Vx.det v) ∈ boxEdges n N a := by
  simp only [boxEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, Prod.exists]
  exact Or.inl (Or.inl ⟨u, v, h, rfl⟩)

/-- `parOK` gives equal degree parities at every point. -/
theorem parOK_spec {A B : List Edge} (h : parOK A B = true) (y : List ℤ) : degC A y % 2 = degC B y % 2 := by
  unfold parOK at h
  rw [List.all_eq_true] at h
  by_cases hy : ∃ e ∈ A ++ B, e.1 = y ∨ e.2 = y
  · obtain ⟨e, he, h1 | h1⟩ := hy
    · have := h e he
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      rw [← h1]; exact this.1
    · have := h e he
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      rw [← h1]; exact this.2
  · push_neg at hy
    have h0 : ∀ L : List Edge, (∀ e ∈ L, e.1 ≠ y ∧ e.2 ≠ y) → degC L y = 0 := by
      intro L hL
      unfold degC
      rw [List.countP_eq_zero]
      intro e he
      simp only [Bool.or_eq_true, beq_iff_eq, not_or]
      exact hL e he
    rw [h0 A (fun e he => hy e (List.mem_append_left _ he)), h0 B (fun e he => hy e (List.mem_append_right _ he))]

/-- **Soundness of the exclusions in the box**: no window of a self-avoiding path of checks, labelled by
membership in a failing minimum-weight correction of least `Φ`, is excluded. -/
theorem box_not_excl {a : Fin n} {c : List ℤ} {E C : Finset (Sym2 (Vx (BoxV n N)))}
    (hC : IsPhiMinFail (boxEdges n N a) (phiBox c) E C) (S : Finset (Sym2 (Vx (BoxV n N))))
    (v0 : BoxV n N) (rest : List (BoxV n N)) (hadj : AdjChain (v0 :: rest)) (hnd : (v0 :: rest).Nodup)
    (hS : ∀ uv ∈ pairs (v0 :: rest), (s(Vx.det uv.1, Vx.det uv.2) ∈ S ↔ s(Vx.det uv.1, Vx.det uv.2) ∉ C)) :
    ¬ Excl n c (patOf S (v0 :: rest)) := by
  rintro ⟨W, hW⟩
  set ws := v0 :: rest with hws
  set w := patOf S ws with hw
  set pts := walkPts n (zeros n) (w.map Prod.fst) with hpts
  -- the points of the window, translated, are the checks of `ws`
  have hwalk : pts.map (addP (pos v0)) = ws.map pos := by
    rw [hpts, ← walkPts_eq_map (length_pos v0), hw, walkPts_patOf S v0 rest hadj]
  have hptsbox : ∀ p ∈ pts, p.length = n ∧ ∃ u : BoxV n N, pos u = addP (pos v0) p := by
    intro p hp
    refine ⟨length_of_mem_walkPts (length_zeros n) hp, ?_⟩
    have : addP (pos v0) p ∈ ws.map pos := by rw [← hwalk]; exact List.mem_map_of_mem hp
    obtain ⟨u, _, hu⟩ := List.mem_map.mp this
    exact ⟨u, hu⟩
  -- the labelled window edges as box edges
  set WE := (pairs ws).map (fun uv => (s(Vx.det uv.1, Vx.det uv.2), decide (s(Vx.det uv.1, Vx.det uv.2) ∉ S)))
    with hWE
  have hz : addP (pos v0) (zeros n) = pos v0 := by have := addP_zeros (pos v0); rwa [length_pos] at this
  have hE0 : (edgesFrom n (zeros n) w).map (fun e => (boxE v0 e.1, e.2)) = WE := by
    have h1 := edgesFrom_patOf S v0 rest hadj
    have h2 := edgesFrom_translate (o := pos v0) (o' := zeros n) (length_pos v0) (length_zeros n) w
    rw [hz] at h2
    rw [h2] at h1
    calc (edgesFrom n (zeros n) w).map (fun e => (boxE v0 e.1, e.2))
        = ((edgesFrom n (zeros n) w).map (fun e => ((addP (pos v0) e.1.1, addP (pos v0) e.1.2), e.2))).map
            (fun e : Edge × Bool => (s(Vx.det (toV v0 e.1.1), Vx.det (toV v0 e.1.2)), e.2)) := by
          rw [List.map_map]; rfl
      _ = ((pairs ws).map (fun uv => ((pos uv.1, pos uv.2), decide (s(Vx.det uv.1, Vx.det uv.2) ∉ S)))).map
            (fun e : Edge × Bool => (s(Vx.det (toV v0 e.1.1), Vx.det (toV v0 e.1.2)), e.2)) := by
          rw [h1]
      _ = WE := by
          rw [List.map_map, hWE]
          apply List.map_congr_left
          intro uv _
          simp [toV_pos]
  -- facts about a window edge
  have hwin : ∀ e ∈ edgesFrom n (zeros n) w, GoodE v0 [e.1] ∧ boxE v0 e.1 ∈ boxEdges n N a ∧
      Vx.b1 ∉ boxE v0 e.1 ∧ (e.2 = true → boxE v0 e.1 ∈ C) ∧ (e.2 = false → boxE v0 e.1 ∉ C) := by
    intro e he
    have hpe := mem_edgesFrom_pts n (zeros n) w e he
    refine ⟨?_, ?_⟩
    · intro f hf
      simp only [List.mem_singleton] at hf
      subst hf
      exact ⟨(hptsbox _ hpe.1).1, (hptsbox _ hpe.2).1, (hptsbox _ hpe.1).2, (hptsbox _ hpe.2).2⟩
    have hmem : (boxE v0 e.1, e.2) ∈ WE := by rw [← hE0]; exact List.mem_map_of_mem (f := fun e => (boxE v0 e.1, e.2)) he
    rw [hWE, List.mem_map] at hmem
    obtain ⟨uv, huv, heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨he1, he2⟩ := heq
    rw [← he1]
    refine ⟨mem_boxEdges_of_l1B (adj_of_mem_pairs hadj huv), by simp [Sym2.mem_iff], ?_, ?_⟩
    · intro hl
      rw [hl] at he2
      have hnS : s(Vx.det uv.1, Vx.det uv.2) ∉ S := by simpa using he2
      by_contra hc
      exact hnS ((hS uv huv).mpr hc)
    · intro hl
      rw [hl] at he2
      have hS' : s(Vx.det uv.1, Vx.det uv.2) ∈ S := by simpa using he2
      exact (hS uv huv).mp hS'
  -- the window edges are distinct
  have hall : ((cEdges n w ++ eEdges n w).map (boxE v0)).Nodup := by
    have hperm : (cEdges n w ++ eEdges n w).Perm ((edgesFrom n (zeros n) w).map Prod.fst) := by
      unfold cEdges eEdges
      rw [← List.map_append]
      exact (List.filter_append_perm _ _).map _
    have hl : ((edgesFrom n (zeros n) w).map Prod.fst).map (boxE v0) = ledges (ws.map Vx.det) := by
      rw [ledges_map_det, List.map_map]
      have := congrArg (List.map Prod.fst) hE0
      rw [List.map_map, hWE, List.map_map] at this
      exact this
    rw [(hperm.map _).nodup_iff, hl]
    exact ledges_nodup (hnd.map (fun _ _ h => Vx.det.inj h))
  -- unpack the witness check
  simp only [checkW, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hW
  obtain ⟨⟨halt, hpar⟩, hsz⟩ := hW
  set X := cEdges n w with hX
  set Y := if W.useE then eEdges n w else [] with hY
  set P := altEdges n W.alt with hP
  have hXmem : ∀ e ∈ X, ∃ e' ∈ edgesFrom n (zeros n) w, e'.2 = true ∧ e'.1 = e := by
    intro e he
    simp only [hX, cEdges, List.mem_map, List.mem_filter] at he
    obtain ⟨e', ⟨he', hl⟩, rfl⟩ := he
    exact ⟨e', he', hl, rfl⟩
  have hYmem : ∀ e ∈ Y, ∃ e' ∈ edgesFrom n (zeros n) w, e'.2 = false ∧ e'.1 = e := by
    intro e he
    rw [hY] at he
    split_ifs at he
    · simp only [eEdges, List.mem_map, List.mem_filter, Bool.not_eq_true'] at he
      obtain ⟨e', ⟨he', hl⟩, rfl⟩ := he
      exact ⟨e', he', hl, rfl⟩
    · simp at he
  have hgoodX : GoodE v0 X := by
    intro e he
    obtain ⟨e', he', -, rfl⟩ := hXmem e he
    exact (hwin e' he').1 _ (by simp)
  have hgoodY : GoodE v0 Y := by
    intro e he
    obtain ⟨e', he', -, rfl⟩ := hYmem e he
    exact (hwin e' he').1 _ (by simp)
  have hgoodP : GoodE v0 P := by
    intro e he
    simp only [hP, altEdges, List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨⟨-, h1⟩, h2⟩ := halt x hx
    have b1 := inBB_box hptsbox h1
    have b2 := inBB_box hptsbox h2
    exact ⟨b1.1, b2.1, b1.2, b2.2⟩
  have hgoodXY : GoodE v0 (X ++ Y) := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact hgoodX e h
    · exact hgoodY e h
  -- the hypotheses of the exchange lemma
  have hXYnd : (X.map (boxE v0) ++ Y.map (boxE v0)).Nodup := by
    rw [hY]
    split_ifs
    · rw [← List.map_append]; exact hall
    · rw [List.map_nil, List.append_nil, ← List.append_nil (X.map (boxE v0))]
      rw [List.map_append] at hall
      exact (List.nodup_append.mp hall).1.append List.nodup_nil (by simp)
  have hXC : ∀ e ∈ X.map (boxE v0), e ∈ C := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    obtain ⟨e', he', hl, rfl⟩ := hXmem f hf
    exact (hwin e' he').2.2.2.1 hl
  have hYC : ∀ e ∈ Y.map (boxE v0), e ∉ C := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    obtain ⟨e', he', hl, rfl⟩ := hYmem f hf
    exact (hwin e' he').2.2.2.2 hl
  have hPg : ∀ e ∈ P.map (boxE v0), e ∈ boxEdges n N a ∧ Vx.b1 ∉ e := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    simp only [hP, altEdges, List.mem_map] at hf
    obtain ⟨x, hx, rfl⟩ := hf
    obtain ⟨⟨hd, h1⟩, h2⟩ := halt x hx
    have b1 := inBB_box hptsbox h1
    have b2 := inBB_box hptsbox h2
    exact ⟨boxE_mem v0 hd b1.1 b1.2 b2.2, by simp [boxE, Sym2.mem_iff]⟩
  have hg : ∀ e ∈ X.map (boxE v0) ++ Y.map (boxE v0) ++ P.map (boxE v0), e ∈ boxEdges n N a ∧ Vx.b1 ∉ e := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · rcases List.mem_append.mp h with h' | h'
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h'
        obtain ⟨e', he', -, rfl⟩ := hXmem f hf
        exact ⟨(hwin e' he').2.1, (hwin e' he').2.2.1⟩
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h'
        obtain ⟨e', he', -, rfl⟩ := hYmem f hf
        exact ⟨(hwin e' he').2.1, (hwin e' he').2.2.1⟩
    · exact hPg e h
  have hodd : oddD (P.map (boxE v0)) = oddD (X.map (boxE v0) ++ Y.map (boxE v0)) := by
    ext u
    simp only [oddD, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← List.map_append, ldeg_map_boxE v0 hgoodP u, ldeg_map_boxE v0 hgoodXY u, Nat.odd_iff, Nat.odd_iff,
      parOK_spec hpar]
  have hex := exchange hC hXYnd hXC hYC (fun e he => (hg e he).1) (fun e he => (hg e he).2) hodd
  simp only [List.length_map] at hex
  rcases hsz with hlt | ⟨⟨heq, hnodup⟩, hphi⟩
  · exact absurd hex.1 (by omega)
  · have h2 := hex.2 heq.symm (nodup_map_boxE v0 hgoodP hnodup)
    rw [phi_map_boxE c v0 hgoodX, phi_map_boxE c v0 hgoodY, phi_map_boxE c v0 hgoodP] at h2
    have hlen : (X.length : ℤ) = Y.length + P.length := by exact_mod_cast heq.symm
    have hmul : 2 * (X.length : ℤ) * phiP c (pos v0) =
        2 * (Y.length : ℤ) * phiP c (pos v0) + 2 * (P.length : ℤ) * phiP c (pos v0) := by rw [hlen]; ring
    linarith

end QEC
