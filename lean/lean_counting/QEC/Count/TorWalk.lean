import QEC.Count.TorDefs
import QEC.Count.Assembly

/-!
# Walks on the torus

Helpers for the assembly of Theorem A′ (`TorAssembly.lean`):

* arithmetic of seam offsets (`qoffZ_congr`, `qoffZ_emod`);
* adjacency (`AdjT`), the neighbour in a direction (`torNext`), and `torNext u (torDir u v) = v` for adjacent `u v`
  (`L ≥ 3`); seam offsets along a step (`qoff_torNext`);
* labelled patterns of vertex lists (`patOfT`): length, directions, labels, recovery of the list from its first vertex
  and its pattern (`eq_of_patOfT`), the offsets of its vertices (`offAt_patOfT`), self-avoidance of the unrolled walk
  (`selfAv_patOfT`, through `torAt`, the torus vertex at an integer offset), weights (`lwt_patOfT`);
* cycles: the edges of a closed vertex list are distinct (`ledges_cycle_nodup`) and have empty boundary (`bd_cycle`).
-/

namespace QEC

open Finset QECComp

namespace TorWalk

/-! ## Arithmetic modulo `L` -/

theorem succ_mod_cases {L a : ℕ} (ha : a < L) :
    ((a + 1) % L = a + 1 ∧ a + 1 < L) ∨ ((a + 1) % L = 0 ∧ a + 1 = L) := by
  rcases Nat.lt_or_ge (a + 1) L with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · have h' : a + 1 = L := by omega
    exact Or.inr ⟨by rw [h', Nat.mod_self], h'⟩

theorem succ_mod_ne {L a : ℕ} (hL : 2 ≤ L) (ha : a < L) : (a + 1) % L ≠ a := by
  rcases succ_mod_cases ha with ⟨h1, -⟩ | ⟨h1, h2⟩ <;> omega

theorem two_cycle_mod {L a b : ℕ} (hL : 3 ≤ L) (ha : a < L) (hb : b < L) (h1 : (a + 1) % L = b)
    (h2 : (b + 1) % L = a) : False := by
  rcases succ_mod_cases ha with ⟨e1, -⟩ | ⟨e1, e2⟩ <;> rcases succ_mod_cases hb with ⟨f1, -⟩ | ⟨f1, f2⟩ <;> omega

/-- The predecessor modulo `L`. -/
theorem pred_mod_of_succ {L a b : ℕ} (hb : b < L) (h : (b + 1) % L = a) : (a + (L - 1)) % L = b := by
  rcases succ_mod_cases hb with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [show a + (L - 1) = b + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  · rw [show a + (L - 1) = b by omega, Nat.mod_eq_of_lt hb]

theorem qoffZ_congr {L : ℕ} {a b : ℤ} (h : a % (L : ℤ) = b % (L : ℤ)) : qoffZ L a = qoffZ L b := by
  unfold qoffZ
  rw [h]

theorem qoffZ_emod (L : ℕ) (q : ℤ) : qoffZ L q % (L : ℤ) = q % (L : ℤ) := by
  unfold qoffZ
  split_ifs
  · exact Int.emod_emod _ _
  · rw [show q % (L : ℤ) - L = q % (L : ℤ) + (-1) * L by ring, Int.add_mul_emod_self_right, Int.emod_emod]

theorem toNat_emod_lt {L : ℕ} (hL : 0 < L) (a : ℤ) : (a % (L : ℤ)).toNat < L := by
  have h0 : 0 ≤ a % (L : ℤ) := Int.emod_nonneg a (by omega)
  have h1 : a % (L : ℤ) < L := Int.emod_lt_of_pos a (by omega)
  omega

theorem toNat_emod_succ {L : ℕ} (hL : 0 < L) (a : ℤ) (c : ℕ) :
    ((a % (L : ℤ)).toNat + c) % L = ((a + c) % (L : ℤ)).toNat := by
  have h0 : 0 ≤ a % (L : ℤ) := Int.emod_nonneg a (by omega)
  have h0' : 0 ≤ (a + c) % (L : ℤ) := Int.emod_nonneg _ (by omega)
  have e : ((((a % (L : ℤ)).toNat + c) % L : ℕ) : ℤ) = ((((a + c) % (L : ℤ)).toNat : ℕ) : ℤ) := by
    rw [Int.natCast_emod, Nat.cast_add, Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h0', Int.emod_add_emod]
  exact_mod_cast e

/-! ## Adjacency and steps -/

/-- Adjacent vertices of the torus. -/
def AdjT {L : ℕ} (u v : TorV L) : Prop := TorStep u v ∨ TorStep v u

theorem adjT_of_mem {L : ℕ} {u v : TorV L} (h : s(Vx.det u, Vx.det v) ∈ torEdges L) : AdjT u v := by
  unfold torEdges at h
  rw [Finset.mem_image] at h
  obtain ⟨⟨a, b⟩, hab, he⟩ := h
  rw [Finset.mem_filter] at hab
  rcases Sym2.eq_iff.mp he with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [← Vx.det.inj e1, ← Vx.det.inj e2]
    exact Or.inl hab.2
  · rw [← Vx.det.inj e1, ← Vx.det.inj e2]
    exact Or.inr hab.2

/-- The neighbour of `u` in direction `d` (`0, 1, 2, 3` = `+x, -x, +y, -y`; `d ≥ 4` acts as `3`). -/
def torNext {L : ℕ} (u : TorV L) (d : ℕ) : TorV L :=
  if d = 0 then (⟨((u.1 : ℕ) + 1) % L, Nat.mod_lt _ u.1.pos⟩, u.2)
  else if d = 1 then (⟨((u.1 : ℕ) + (L - 1)) % L, Nat.mod_lt _ u.1.pos⟩, u.2)
  else if d = 2 then (u.1, ⟨((u.2 : ℕ) + 1) % L, Nat.mod_lt _ u.2.pos⟩)
  else (u.1, ⟨((u.2 : ℕ) + (L - 1)) % L, Nat.mod_lt _ u.2.pos⟩)

theorem torNext_zero {L : ℕ} (u : TorV L) :
    torNext u 0 = (⟨((u.1 : ℕ) + 1) % L, Nat.mod_lt _ u.1.pos⟩, u.2) := by
  unfold torNext
  rw [ite_eq_left rfl]

theorem torNext_one {L : ℕ} (u : TorV L) :
    torNext u 1 = (⟨((u.1 : ℕ) + (L - 1)) % L, Nat.mod_lt _ u.1.pos⟩, u.2) := by
  unfold torNext
  rw [ite_eq_right (by omega), ite_eq_left rfl]

theorem torNext_two {L : ℕ} (u : TorV L) :
    torNext u 2 = (u.1, ⟨((u.2 : ℕ) + 1) % L, Nat.mod_lt _ u.2.pos⟩) := by
  unfold torNext
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem torNext_three {L : ℕ} (u : TorV L) :
    torNext u 3 = (u.1, ⟨((u.2 : ℕ) + (L - 1)) % L, Nat.mod_lt _ u.2.pos⟩) := by
  unfold torNext
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem torDir_lt {L : ℕ} (u v : TorV L) : torDir u v < 4 := by
  unfold torDir
  split_ifs <;> omega

theorem torNext_torDir {L : ℕ} (hL : 3 ≤ L) {u v : TorV L} (h : AdjT u v) : torNext u (torDir u v) = v := by
  rcases h with (⟨h2, h1⟩ | ⟨h1, h2⟩) | (⟨h2, h1⟩ | ⟨h1, h2⟩)
  · have hd : torDir u v = 0 := by
      unfold torDir
      rw [ite_eq_left ⟨h2, h1⟩]
    rw [hd, torNext_zero]
    exact Prod.ext (Fin.ext h1) h2
  · have hne : u.2 ≠ v.2 := by
      intro he
      rw [← he] at h2
      exact succ_mod_ne (by omega) u.2.isLt h2
    have hd : torDir u v = 2 := by
      unfold torDir
      rw [ite_eq_right (fun h => hne h.1), ite_eq_right (fun h => hne h.1), ite_eq_left ⟨h1, h2⟩]
    rw [hd, torNext_two]
    exact Prod.ext h1 (Fin.ext h2)
  · have hd : torDir u v = 1 := by
      unfold torDir
      rw [ite_eq_right (fun h => two_cycle_mod hL u.1.isLt v.1.isLt h.2 h1), ite_eq_left ⟨h2.symm, h1⟩]
    rw [hd, torNext_one]
    exact Prod.ext (Fin.ext (pred_mod_of_succ v.1.isLt h1)) h2.symm
  · have hne : u.2 ≠ v.2 := by
      intro he
      rw [he] at h2
      exact succ_mod_ne (by omega) v.2.isLt h2
    have hd : torDir u v = 3 := by
      unfold torDir
      rw [ite_eq_right (fun h => hne h.1), ite_eq_right (fun h => hne h.1),
        ite_eq_right (fun h => two_cycle_mod hL u.2.isLt v.2.isLt h.2 h2)]
    rw [hd, torNext_three]
    exact Prod.ext h1.symm (Fin.ext (pred_mod_of_succ v.2.isLt h2))

theorem torNext_fst_emod {L : ℕ} (u : TorV L) (d : ℕ) :
    (((torNext u d).1 : ℕ) : ℤ) % (L : ℤ) = (((u.1 : ℕ) : ℤ) + dxOf d) % (L : ℤ) := by
  have hL : 0 < L := u.1.pos
  by_cases h0 : d = 0
  · subst h0
    have e2 : dxOf 0 = 1 := rfl
    rw [torNext_zero, e2, Fin.val_mk, Int.natCast_emod, Int.emod_emod, Nat.cast_add, Nat.cast_one]
  by_cases h1 : d = 1
  · subst h1
    have e2 : dxOf 1 = -1 := rfl
    rw [torNext_one, e2, Fin.val_mk, Int.natCast_emod, Int.emod_emod, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ L),
      Nat.cast_one, show ((u.1 : ℕ) : ℤ) + ((L : ℤ) - 1) = (((u.1 : ℕ) : ℤ) + -1) + 1 * (L : ℤ) by ring,
      Int.add_mul_emod_self_right]
  · have hx : (torNext u d).1 = u.1 := by
      unfold torNext
      rw [ite_eq_right h0, ite_eq_right h1]
      split_ifs <;> rfl
    have hdx : dxOf d = 0 := by
      unfold dxOf
      rw [ite_eq_right h0, ite_eq_right h1]
    rw [hx, hdx, add_zero]

/-- The seam offset after a step. -/
theorem qoff_torNext {L : ℕ} (u : TorV L) (d : ℕ) : qoff (torNext u d) = nxtT L (qoff u) d := by
  unfold qoff nxtT
  apply qoffZ_congr
  rw [torNext_fst_emod, Int.add_emod (((u.1 : ℕ) : ℤ)), Int.add_emod (qoffZ L _), qoffZ_emod]

/-! ## Labelled patterns of vertex lists -/

/-- Consecutive vertices of the list are adjacent. -/
def AdjChainT {L : ℕ} : List (TorV L) → Prop
  | u :: v :: rest => AdjT u v ∧ AdjChainT (v :: rest)
  | _ => True

theorem adjChainT_of_isChain {L : ℕ} {R : Finset (Sym2 (Vx (TorV L)))} (hR : R ⊆ torEdges L) :
    ∀ vs : List (TorV L), (vs.map Vx.det).IsChain (decGraph R).Adj → AdjChainT vs
  | [], _ => trivial
  | [_], _ => trivial
  | u :: v :: rest, h => by
    simp only [List.map_cons, List.isChain_cons_cons] at h
    exact ⟨adjT_of_mem (hR h.1.2), adjChainT_of_isChain hR (v :: rest) h.2⟩

theorem length_patOfT {L : ℕ} (S : Finset (Sym2 (Vx (TorV L)))) :
    ∀ vs : List (TorV L), (patOfT S vs).length = vs.length - 1
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by simp [patOfT, length_patOfT S (v :: rest)]

theorem dirOK_patOfT {L : ℕ} (S : Finset (Sym2 (Vx (TorV L)))) : ∀ vs : List (TorV L), DirOK 2 (patOfT S vs)
  | [] => by simp [patOfT, DirOK]
  | [_] => by simp [patOfT, DirOK]
  | u :: v :: rest => by
    intro x hx
    simp only [patOfT, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have := torDir_lt u v
      show torDir u v < 2 * 2
      omega
    · exact dirOK_patOfT S (v :: rest) x hx

theorem patOfT_congr {L : ℕ} {S S' : Finset (Sym2 (Vx (TorV L)))} : ∀ vs : List (TorV L),
    (∀ e ∈ ledges (vs.map Vx.det), (e ∈ S ↔ e ∈ S')) → patOfT S vs = patOfT S' vs
  | [], _ => rfl
  | [_], _ => rfl
  | u :: v :: rest, h => by
    have h1 : s(Vx.det u, Vx.det v) ∈ S ↔ s(Vx.det u, Vx.det v) ∈ S' := h _ (by simp)
    have h2 : ∀ e ∈ ledges ((v :: rest).map Vx.det), (e ∈ S ↔ e ∈ S') := by
      intro e he
      apply h e
      simp only [List.map_cons, ledges_cons_cons, List.mem_cons] at he ⊢
      exact Or.inr he
    simp only [patOfT]
    rw [patOfT_congr (v :: rest) h2]
    simp [h1]

theorem patOfT_eq_labels {L : ℕ} {S S' : Finset (Sym2 (Vx (TorV L)))} : ∀ vs : List (TorV L),
    patOfT S vs = patOfT S' vs → ∀ e ∈ ledges (vs.map Vx.det), (e ∈ S ↔ e ∈ S')
  | [], _, e, he => by simp at he
  | [_], _, e, he => by simp at he
  | u :: v :: rest, h, e, he => by
    simp only [patOfT, List.cons.injEq, Prod.mk.injEq] at h
    simp only [List.map_cons, ledges_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · have h2 := h.1.2
      by_cases h1 : s(Vx.det u, Vx.det v) ∈ S <;> by_cases h3 : s(Vx.det u, Vx.det v) ∈ S' <;> simp_all
    · exact patOfT_eq_labels (v :: rest) h.2 e (by simpa using he)

/-- A vertex list is determined by its first vertex and its pattern. -/
theorem eq_of_patOfT {L : ℕ} (hL : 3 ≤ L) {S S' : Finset (Sym2 (Vx (TorV L)))} :
    ∀ (u : TorV L) (r r' : List (TorV L)), AdjChainT (u :: r) → AdjChainT (u :: r') →
      patOfT S (u :: r) = patOfT S' (u :: r') → r = r'
  | _, [], [], _, _, _ => rfl
  | _, [], _ :: _, _, _, h => by simp [patOfT] at h
  | _, _ :: _, [], _, _, h => by simp [patOfT] at h
  | u, v :: r, v' :: r', h1, h2, h => by
    simp only [patOfT, List.cons.injEq, Prod.mk.injEq] at h
    have hv : v = v' := by
      rw [← torNext_torDir hL h1.1, ← torNext_torDir hL h2.1, h.1.1]
    subst hv
    rw [eq_of_patOfT hL v r r' h1.2 h2.2 h.2]

/-- The offsets of the vertices along the pattern of a vertex list. -/
theorem offAt_patOfT {L : ℕ} (hL : 3 ≤ L) (S : Finset (Sym2 (Vx (TorV L)))) :
    ∀ (u : TorV L) (rest : List (TorV L)), AdjChainT (u :: rest) → ∀ (i : ℕ) (hi : i < rest.length + 1),
      offAt (nxtT L) (qoff u) (patOfT S (u :: rest)) i = qoff ((u :: rest)[i]'hi)
  | u, rest, _, 0, _ => by simp [offAt]
  | u, [], _, i + 1, hi => by simp at hi
  | u, v :: rest, h, i + 1, hi => by
    have ih := offAt_patOfT hL S v rest h.2 i (by simp at hi ⊢; omega)
    have hstep : nxtT L (qoff u) (torDir u v) = qoff v := by
      rw [← qoff_torNext, torNext_torDir hL h.1]
    unfold offAt at ih ⊢
    simp only [patOfT, List.take_succ_cons, List.map_cons, List.foldl_cons, hstep]
    rw [ih]
    rfl

/-- The torus vertex at the integer offset `p` (two coordinates) from `v0`. -/
def torAt {L : ℕ} (v0 : TorV L) (p : List ℤ) : TorV L :=
  (⟨((((v0.1 : ℕ) : ℤ) + p.getD 0 0) % (L : ℤ)).toNat, toNat_emod_lt v0.1.pos _⟩,
    ⟨((((v0.2 : ℕ) : ℤ) + p.getD 1 0) % (L : ℤ)).toNat, toNat_emod_lt v0.1.pos _⟩)

theorem torAt_zeros {L : ℕ} (v0 : TorV L) : torAt v0 (zeros 2) = v0 := by
  have h1 : ((((v0.1 : ℕ) : ℤ) + (zeros 2).getD 0 0) % (L : ℤ)).toNat = v0.1 := by
    rw [show (zeros 2).getD 0 0 = 0 from rfl, add_zero,
      Int.emod_eq_of_lt (by omega) (by have := v0.1.isLt; omega)]
    simp
  have h2 : ((((v0.2 : ℕ) : ℤ) + (zeros 2).getD 1 0) % (L : ℤ)).toNat = v0.2 := by
    rw [show (zeros 2).getD 1 0 = 0 from rfl, add_zero,
      Int.emod_eq_of_lt (by omega) (by have := v0.2.isLt; omega)]
    simp
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

theorem torAt_step {L : ℕ} (v0 : TorV L) {o : List ℤ} (ho : o.length = 2) {d : ℕ} (hd : d < 4) :
    torAt v0 (addP o (vecOf 2 d)) = torNext (torAt v0 o) d := by
  have hL : 0 < L := v0.1.pos
  have g0 : (addP o (vecOf 2 d)).getD 0 0 = o.getD 0 0 + (vecOf 2 d).getD 0 0 :=
    getD_addP _ _ _ (by omega) (by simp)
  have g1 : (addP o (vecOf 2 d)).getD 1 0 = o.getD 1 0 + (vecOf 2 d).getD 1 0 :=
    getD_addP _ _ _ (by omega) (by simp)
  rw [getD_vecOf 2 d 0 (by omega)] at g0
  rw [getD_vecOf 2 d 1 (by omega)] at g1
  have hLm1 : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  set x0 := ((v0.1 : ℕ) : ℤ) with hx0
  set y0 := ((v0.2 : ℕ) : ℤ) with hy0
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl
  · rw [torNext_zero]
    norm_num at g0 g1
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show ((x0 + (addP o (vecOf 2 0)).getD 0 0) % (L : ℤ)).toNat =
        (((x0 + o.getD 0 0) % (L : ℤ)).toNat + 1) % L
      rw [toNat_emod_succ hL]
      simp only [List.getD_eq_getElem?_getD]
      rw [g0, Nat.cast_one, add_assoc]
    · show ((y0 + (addP o (vecOf 2 0)).getD 1 0) % (L : ℤ)).toNat = ((y0 + o.getD 1 0) % (L : ℤ)).toNat
      simp only [List.getD_eq_getElem?_getD]
      rw [g1]
  · rw [torNext_one]
    norm_num at g0 g1
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show ((x0 + (addP o (vecOf 2 1)).getD 0 0) % (L : ℤ)).toNat =
        (((x0 + o.getD 0 0) % (L : ℤ)).toNat + (L - 1)) % L
      rw [toNat_emod_succ hL]
      simp only [List.getD_eq_getElem?_getD]
      rw [g0, hLm1, show x0 + o[0]?.getD 0 + ((L : ℤ) - 1) = (x0 + (o[0]?.getD 0 + -1)) + 1 * (L : ℤ) by ring,
        Int.add_mul_emod_self_right]
    · show ((y0 + (addP o (vecOf 2 1)).getD 1 0) % (L : ℤ)).toNat = ((y0 + o.getD 1 0) % (L : ℤ)).toNat
      simp only [List.getD_eq_getElem?_getD]
      rw [g1]
  · rw [torNext_two]
    norm_num at g0 g1
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show ((x0 + (addP o (vecOf 2 2)).getD 0 0) % (L : ℤ)).toNat = ((x0 + o.getD 0 0) % (L : ℤ)).toNat
      simp only [List.getD_eq_getElem?_getD]
      rw [g0]
    · show ((y0 + (addP o (vecOf 2 2)).getD 1 0) % (L : ℤ)).toNat =
        (((y0 + o.getD 1 0) % (L : ℤ)).toNat + 1) % L
      rw [toNat_emod_succ hL]
      simp only [List.getD_eq_getElem?_getD]
      rw [g1, Nat.cast_one, add_assoc]
  · rw [torNext_three]
    norm_num at g0 g1
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show ((x0 + (addP o (vecOf 2 3)).getD 0 0) % (L : ℤ)).toNat = ((x0 + o.getD 0 0) % (L : ℤ)).toNat
      simp only [List.getD_eq_getElem?_getD]
      rw [g0]
    · show ((y0 + (addP o (vecOf 2 3)).getD 1 0) % (L : ℤ)).toNat =
        (((y0 + o.getD 1 0) % (L : ℤ)).toNat + (L - 1)) % L
      rw [toNat_emod_succ hL]
      simp only [List.getD_eq_getElem?_getD]
      rw [g1, hLm1, show y0 + o[1]?.getD 0 + ((L : ℤ) - 1) = (y0 + (o[1]?.getD 0 + -1)) + 1 * (L : ℤ) by ring,
        Int.add_mul_emod_self_right]

/-- The unrolled walk of the pattern of a vertex list, mapped back to the torus, is the list. -/
theorem walkPts_map_torAt {L : ℕ} (hL : 3 ≤ L) (S : Finset (Sym2 (Vx (TorV L)))) (v0 : TorV L) :
    ∀ (u : TorV L) (rest : List (TorV L)) (o : List ℤ), o.length = 2 → torAt v0 o = u → AdjChainT (u :: rest) →
      (walkPts 2 o ((patOfT S (u :: rest)).map Prod.fst)).map (torAt v0) = u :: rest
  | u, [], o, _, hu, _ => by simp [patOfT, hu]
  | u, v :: rest, o, ho, hu, h => by
    have hv : torAt v0 (addP o (vecOf 2 (torDir u v))) = v := by
      rw [torAt_step v0 ho (torDir_lt u v), hu, torNext_torDir hL h.1]
    have ih := walkPts_map_torAt hL S v0 v rest (addP o (vecOf 2 (torDir u v))) (by simp [ho]) hv h.2
    simp only [patOfT, List.map_cons, walkPts_cons]
    rw [hu]
    exact congrArg (u :: ·) ih

/-- The unrolled walk of the pattern of a simple path on the torus is self-avoiding. -/
theorem selfAv_patOfT {L : ℕ} (hL : 3 ≤ L) (S : Finset (Sym2 (Vx (TorV L)))) {v0 : TorV L}
    {rest : List (TorV L)} (h : AdjChainT (v0 :: rest)) (hnd : (v0 :: rest).Nodup) :
    SelfAv 2 (patOfT S (v0 :: rest)) := by
  unfold SelfAv
  have h1 := walkPts_map_torAt hL S v0 v0 rest (zeros 2) (by simp) (torAt_zeros v0) h
  rw [← h1] at hnd
  exact hnd.of_map _

/-- The weight of the edges of a vertex list is the weight of its pattern. -/
theorem lwt_patOfT {L : ℕ} (ωE ωC : ℝ) (S : Finset (Sym2 (Vx (TorV L)))) :
    ∀ vs : List (TorV L), lwt (fun e => if e ∈ S then ωE else ωC) (vs.map Vx.det) = wtW ωE ωC (patOfT S vs)
  | [] => by simp [patOfT, wtW]
  | [_] => by simp [patOfT, wtW]
  | u :: v :: rest => by
    simp only [List.map_cons, lwt_cons_cons, patOfT, wtW, List.prod_cons]
    rw [← List.map_cons, lwt_patOfT ωE ωC S (v :: rest)]
    simp only [wtW, decide_not]
    by_cases h : s(Vx.det u, Vx.det v) ∈ S <;> simp [h]

/-! ## Cycles -/

/-- The edges of a closed list of at least three distinct vertices are distinct. -/
theorem ledges_cycle_nodup {X : Type*} {v0 : X} {rest : List X} (hnd : (v0 :: rest).Nodup)
    (h2 : 2 ≤ rest.length) : (ledges ((v0 :: rest) ++ [v0])).Nodup := by
  obtain ⟨r1, r2, rs, rfl⟩ : ∃ r1 r2 rs, rest = r1 :: r2 :: rs := by
    match rest, h2 with
    | r1 :: r2 :: rs, _ => exact ⟨r1, r2, rs, rfl⟩
  rw [Assembly.ledges_append_single v0 (v0 :: r1 :: r2 :: rs) (List.cons_ne_nil _ _), List.nodup_append]
  refine ⟨ledges_nodup hnd, List.nodup_singleton _, ?_⟩
  intro e he e' he' hee'
  rw [List.mem_singleton] at he'
  subst he'
  subst hee'
  rw [List.getLast_cons_cons, List.getLast_cons_cons] at he
  have hlast : (r2 :: rs).getLast (List.cons_ne_nil _ _) ∈ r2 :: rs := List.getLast_mem _
  have hv0 : v0 ∉ r1 :: r2 :: rs := (List.nodup_cons.mp hnd).1
  have hr1 : r1 ∉ r2 :: rs := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  rw [ledges_cons_cons, List.mem_cons] at he
  rcases he with he | he
  · rcases Sym2.eq_iff.mp he with ⟨e1, -⟩ | ⟨e1, -⟩
    · rw [e1] at hlast
      exact hv0 (List.mem_cons_of_mem _ hlast)
    · rw [e1] at hlast
      exact hr1 hlast
  · exact hv0 (mem_of_mem_ledges he (Sym2.mem_mk_right _ _))

theorem vdeg_pedges_of_nodup {X : Type*} [DecidableEq X] {l : List X} (hl : (ledges l).Nodup) (z : X) :
    vdeg (pedges l) z = (ledges l).countP (fun e => z ∈ e) := by
  unfold vdeg pedges
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter _)]
  congr 1
  ext e
  simp

/-- A closed list of at least three distinct vertices has edges of empty boundary. -/
theorem bd_cycle {V : Type*} [Fintype V] [DecidableEq V] {v0 : V} {rest : List V} (hnd : (v0 :: rest).Nodup)
    (h2 : 2 ≤ rest.length) : bd (pedges ((v0 :: rest).map Vx.det ++ [Vx.det v0])) = ∅ := by
  have hlnd : ((v0 :: rest).map Vx.det).Nodup := hnd.map (fun a b h => Vx.det.inj h)
  have hcyc : (ledges ((v0 :: rest).map Vx.det ++ [Vx.det v0])).Nodup :=
    ledges_cycle_nodup (v0 := Vx.det v0) (rest := rest.map Vx.det) hlnd (by simpa using h2)
  obtain ⟨r1, r2, rs, rfl⟩ : ∃ r1 r2 rs, rest = r1 :: r2 :: rs := by
    match rest, h2 with
    | r1 :: r2 :: rs, _ => exact ⟨r1, r2, rs, rfl⟩
  have hne0 : (v0 :: r1 :: r2 :: rs).map Vx.det ≠ [] := by simp
  have hlast_eq : ((v0 :: r1 :: r2 :: rs).map Vx.det).getLast hne0 =
      Vx.det ((r2 :: rs).getLast (List.cons_ne_nil _ _)) := by
    rw [List.getLast_map, List.getLast_cons_cons, List.getLast_cons_cons]
  have hne : ((v0 :: r1 :: r2 :: rs).map Vx.det).getLast hne0 ≠ Vx.det v0 := by
    rw [hlast_eq]
    intro he
    have hmem := List.getLast_mem (List.cons_ne_nil r2 rs)
    rw [Vx.det.inj he] at hmem
    exact (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ hmem)
  ext v
  simp only [mem_bd, Finset.notMem_empty, iff_false, Nat.not_odd_iff_even]
  rw [vdeg_pedges_of_nodup hcyc, Assembly.ledges_append_single _ _ hne0, List.countP_append]
  have h := even_countP_ledges (Vx.det v) hlnd hne0
  rw [List.getLast?_eq_some_getLast hne0] at h
  have hhd : ((v0 :: r1 :: r2 :: rs).map Vx.det).head? = some (Vx.det v0) := rfl
  rw [hhd] at h
  set last := ((v0 :: r1 :: r2 :: rs).map Vx.det).getLast hne0 with hlast
  have key : ([s(last, Vx.det v0)].countP (fun e => Vx.det v ∈ e)) =
      (if last = Vx.det v then 1 else 0) + (if Vx.det v0 = Vx.det v then 1 else 0) := by
    rw [List.countP_cons, List.countP_nil, zero_add]
    by_cases h1 : last = Vx.det v
    · have h3 : Vx.det v0 ≠ Vx.det v := fun h3 => hne (h1.trans h3.symm)
      simp [h1, h3]
    · by_cases h3 : Vx.det v0 = Vx.det v
      · simp [h1, h3]
      · have : Vx.det v ∉ s(last, Vx.det v0) := by
          rw [Sym2.mem_iff]
          rintro (h4 | h4)
          · exact h1 h4.symm
          · exact h3 h4.symm
        simp [this, h1, h3]
  rw [key]
  simp only [Option.some.injEq] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by omega⟩

end TorWalk

end QEC
