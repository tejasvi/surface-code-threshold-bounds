import QEC.Count.TorDefs
import QEC.Count.BoxSound

/-!
# Soundness of the seam exclusions on the torus

Let `C` be a failing minimum-weight correction of least `Φ = phiTor L` for the toric code, and `vs` a self-avoiding
path of the torus whose edges lie in the residual `C ∆ E`, labelled by `patOfT E` (label `true` = not in `E` = in
`C`). Then no window of `2..M` edges of `vs` is excluded by the seam rules (`tor_window_not_excl`), provided
`L0 ≤ L` and `2M + 2 < L`.

A checked witness `checkWT L0 o u W` (`o` = the seam offset of the window's first vertex) gives an alternative edge
list of unit steps inside the bounding box of the window. Relative points `p` are mapped to the torus by
`torPt v p = v + p (mod L)`, which is injective on points with coordinates of absolute value at most `m` when
`2m < L`. The column of `torPt v p` is `L·A + B` for `(A, B) = phiT (qoff v + p.x)`, so `Φ` of the image of an edge
list is `L·A + B` for its `phiTE`. The exchange lemma `exchangeT` then contradicts the size or the `Φ` inequality
(`lexLt` and `|ΔB| < L0 ≤ L`).
-/

namespace QEC

open Finset QECComp
open scoped symmDiff

/-! ## Residues -/

theorem toNat_emod_lt {L : ℕ} (hL : 0 < L) (z : ℤ) : (z % (L : ℤ)).toNat < L := by
  have h1 := Int.emod_nonneg z (show (L : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos z (show (0 : ℤ) < L by omega)
  omega

/-- The residue of an integer in `[-L, 2L)` modulo `L`. -/
theorem emod_cases {L : ℕ} {z : ℤ} (h1 : -(L : ℤ) ≤ z) (h2 : z < 2 * L) :
    z % (L : ℤ) = if z < 0 then z + L else if z < L then z else z - L := by
  split_ifs with ha hb
  · rw [← Int.add_mul_emod_self_left z L 1, mul_one]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · exact Int.emod_eq_of_lt (by omega) hb
  · rw [← Int.add_mul_emod_self_left z L (-1), show z + (L : ℤ) * (-1) = z - L by ring]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-! ## Relative points on the torus -/

variable {L : ℕ}

/-- The torus vertex at the relative position `p` (two integer coordinates) from `v`. -/
def torPt (v : TorV L) (p : List ℤ) : TorV L :=
  (⟨((((v.1 : ℕ) : ℤ) + p.getD 0 0) % (L : ℤ)).toNat, toNat_emod_lt v.1.pos _⟩,
   ⟨((((v.2 : ℕ) : ℤ) + p.getD 1 0) % (L : ℤ)).toNat, toNat_emod_lt v.1.pos _⟩)

theorem torPt_fst (v : TorV L) (p : List ℤ) :
    (((torPt v p).1 : ℕ) : ℤ) = (((v.1 : ℕ) : ℤ) + p.getD 0 0) % (L : ℤ) := by
  simp only [torPt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := v.1.pos; omega))

theorem torPt_snd (v : TorV L) (p : List ℤ) :
    (((torPt v p).2 : ℕ) : ℤ) = (((v.2 : ℕ) : ℤ) + p.getD 1 0) % (L : ℤ) := by
  simp only [torPt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := v.1.pos; omega))

theorem torPt_ext {u v : TorV L} (h1 : (((u.1 : ℕ) : ℤ)) = (((v.1 : ℕ) : ℤ)))
    (h2 : (((u.2 : ℕ) : ℤ)) = (((v.2 : ℕ) : ℤ))) : u = v :=
  Prod.ext (Fin.ext (by exact_mod_cast h1)) (Fin.ext (by exact_mod_cast h2))

theorem torPt_add (v : TorV L) {p q : List ℤ} (hp : p.length = 2) (hq : q.length = 2) :
    torPt (torPt v p) q = torPt v (addP p q) := by
  apply torPt_ext
  · rw [torPt_fst, torPt_fst, torPt_fst, getD_addP _ _ _ (by omega) (by omega), Int.emod_add_emod, add_assoc]
  · rw [torPt_snd, torPt_snd, torPt_snd, getD_addP _ _ _ (by omega) (by omega), Int.emod_add_emod, add_assoc]

theorem torPt_zeros (v : TorV L) : torPt v (zeros 2) = v := by
  apply torPt_ext
  · rw [torPt_fst]
    simp only [zeros, List.replicate, List.getD_cons_zero, add_zero]
    exact Int.emod_eq_of_lt (by omega) (by have := v.1.2; omega)
  · rw [torPt_snd]
    simp only [zeros, List.replicate, List.getD_cons_succ, List.getD_cons_zero, add_zero]
    exact Int.emod_eq_of_lt (by omega) (by have := v.2.2; omega)

theorem vecOf_two_0 : vecOf 2 0 = [1, 0] := by decide
theorem vecOf_two_1 : vecOf 2 1 = [-1, 0] := by decide
theorem vecOf_two_2 : vecOf 2 2 = [0, 1] := by decide
theorem vecOf_two_3 : vecOf 2 3 = [0, -1] := by decide

theorem succ_mod_cases {a : ℕ} (ha : a < L) : (a + 1) % L = if a + 1 < L then a + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [show a + 1 = L by omega, Nat.mod_self]

/-! ## Torus steps -/

theorem mem_torEdges {u v : TorV L} : s(Vx.det u, Vx.det v) ∈ torEdges L ↔ TorStep u v ∨ TorStep v u := by
  unfold torEdges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    rw [Finset.mem_filter] at hab
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Vx.det.inj h1, ← Vx.det.inj h2]
      exact hab.2
    · right
      rw [← Vx.det.inj h1, ← Vx.det.inj h2]
      exact hab.2
  · rintro (h | h)
    · exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩, rfl⟩
    · exact ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩,
        Sym2.eq_swap⟩

theorem torDir_lt (u v : TorV L) : torDir u v < 4 := by
  unfold torDir
  split_ifs <;> omega

/-- The step in the direction `torDir u v` from `u` leads to the neighbour `v`. -/
theorem torPt_torDir {u v : TorV L} (h : TorStep u v ∨ TorStep v u) : torPt u (vecOf 2 (torDir u v)) = v := by
  have hu1 := u.1.2
  have hu2 := u.2.2
  have hv1 := v.1.2
  have hv2 := v.2.2
  unfold torDir
  split_ifs with h0 h1 h2
  · rw [vecOf_two_0]
    obtain ⟨e2, e1⟩ := h0
    apply torPt_ext
    · rw [torPt_fst, ← e1, succ_mod_cases hu1]
      simp only [List.getD_cons_zero]
      rw [emod_cases (by omega) (by omega)]
      split_ifs <;> push_cast <;> omega
    · rw [torPt_snd, ← e2]
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
      exact Int.emod_eq_of_lt (by omega) (by omega)
  · rw [vecOf_two_1]
    obtain ⟨e2, e1⟩ := h1
    apply torPt_ext
    · rw [torPt_fst, ← e1, succ_mod_cases hv1]
      simp only [List.getD_cons_zero]
      split_ifs with hh
      · push_cast
        rw [show ((v.1 : ℕ) : ℤ) + 1 + -1 = ((v.1 : ℕ) : ℤ) by ring]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      · push_cast
        rw [emod_cases (by omega) (by omega)]
        split_ifs <;> omega
    · rw [torPt_snd, ← e2]
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
      exact Int.emod_eq_of_lt (by omega) (by omega)
  · rw [vecOf_two_2]
    obtain ⟨e1, e2⟩ := h2
    apply torPt_ext
    · rw [torPt_fst, ← e1]
      simp only [List.getD_cons_zero, add_zero]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    · rw [torPt_snd, ← e2, succ_mod_cases hu2]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [emod_cases (by omega) (by omega)]
      split_ifs <;> push_cast <;> omega
  · rw [vecOf_two_3]
    have h3 : u.1 = v.1 ∧ ((v.2 : ℕ) + 1) % L = u.2 := by
      rcases h with (hs | hs) | (hs | hs)
      · exact absurd hs h0
      · exact absurd hs h2
      · exact absurd ⟨hs.1.symm, hs.2⟩ h1
      · exact ⟨hs.1.symm, hs.2⟩
    obtain ⟨e1, e2⟩ := h3
    apply torPt_ext
    · rw [torPt_fst, ← e1]
      simp only [List.getD_cons_zero, add_zero]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    · rw [torPt_snd, ← e2, succ_mod_cases hv2]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      split_ifs with hh
      · push_cast
        rw [show ((v.2 : ℕ) : ℤ) + 1 + -1 = ((v.2 : ℕ) : ℤ) by ring]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      · push_cast
        rw [emod_cases (by omega) (by omega)]
        split_ifs <;> omega

/-- A unit step from a torus vertex is an edge of the toric code. -/
theorem step_mem_torEdges (u : TorV L) {d : ℕ} (hd : d < 4) :
    s(Vx.det u, Vx.det (torPt u (vecOf 2 d))) ∈ torEdges L := by
  have hu1 := u.1.2
  have hu2 := u.2.2
  rw [mem_torEdges]
  have hcase : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl
  · left; left
    refine ⟨?_, ?_⟩
    · apply Fin.ext
      have := torPt_snd u (vecOf 2 0)
      rw [vecOf_two_0] at this ⊢
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero] at this
      rw [Int.emod_eq_of_lt (by omega) (by omega)] at this
      exact_mod_cast this.symm
    · have := torPt_fst u (vecOf 2 0)
      rw [vecOf_two_0] at this ⊢
      simp only [List.getD_cons_zero] at this
      rw [succ_mod_cases hu1]
      rw [emod_cases (by omega) (by omega)] at this
      split_ifs at this ⊢ <;> omega
  · right; left
    refine ⟨?_, ?_⟩
    · apply Fin.ext
      have := torPt_snd u (vecOf 2 1)
      rw [vecOf_two_1] at this ⊢
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero] at this
      rw [Int.emod_eq_of_lt (by omega) (by omega)] at this
      exact_mod_cast this
    · have := torPt_fst u (vecOf 2 1)
      rw [vecOf_two_1] at this ⊢
      simp only [List.getD_cons_zero] at this
      have hlt := (torPt u [-1, 0]).1.2
      rw [succ_mod_cases hlt]
      rw [emod_cases (by omega) (by omega)] at this
      split_ifs at this ⊢ <;> omega
  · left; right
    refine ⟨?_, ?_⟩
    · apply Fin.ext
      have := torPt_fst u (vecOf 2 2)
      rw [vecOf_two_2] at this ⊢
      simp only [List.getD_cons_zero, add_zero] at this
      rw [Int.emod_eq_of_lt (by omega) (by omega)] at this
      exact_mod_cast this.symm
    · have := torPt_snd u (vecOf 2 2)
      rw [vecOf_two_2] at this ⊢
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this
      rw [succ_mod_cases hu2]
      rw [emod_cases (by omega) (by omega)] at this
      split_ifs at this ⊢ <;> omega
  · right; right
    refine ⟨?_, ?_⟩
    · apply Fin.ext
      have := torPt_fst u (vecOf 2 3)
      rw [vecOf_two_3] at this ⊢
      simp only [List.getD_cons_zero, add_zero] at this
      rw [Int.emod_eq_of_lt (by omega) (by omega)] at this
      exact_mod_cast this
    · have := torPt_snd u (vecOf 2 3)
      rw [vecOf_two_3] at this ⊢
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this
      have hlt := (torPt u [0, -1]).2.2
      rw [succ_mod_cases hlt]
      rw [emod_cases (by omega) (by omega)] at this
      split_ifs at this ⊢ <;> omega

/-! ## Bounded relative points -/

/-- A relative point with two coordinates of absolute value at most `m`. -/
def Bd (m : ℕ) (q : List ℤ) : Prop :=
  q.length = 2 ∧ -(m : ℤ) ≤ q.getD 0 0 ∧ q.getD 0 0 ≤ m ∧ -(m : ℤ) ≤ q.getD 1 0 ∧ q.getD 1 0 ≤ m

theorem list_two_eq {q : List ℤ} (hq : q.length = 2) : q = [q.getD 0 0, q.getD 1 0] := by
  match q, hq with
  | [_, _], _ => rfl

theorem bd_zeros : Bd 0 (zeros 2) := by
  refine ⟨by simp, ?_⟩
  simp [zeros]

/-- The points of a walk of `k'` steps from a point bounded by `k` are bounded by `k + k'`. -/
theorem bd_walkPts : ∀ (o : List ℤ) (ds : List ℕ) (k : ℕ), Bd k o → ∀ p ∈ walkPts 2 o ds, Bd (k + ds.length) p
  | o, [], k, ho, p, hp => by
    simp only [walkPts_nil, List.mem_singleton] at hp
    subst hp
    simpa using ho
  | o, d :: ds, k, ho, p, hp => by
    simp only [walkPts_cons, List.mem_cons] at hp
    obtain ⟨h0, h1, h2, h3, h4⟩ := ho
    rcases hp with rfl | hp
    · refine ⟨h0, ?_, ?_, ?_, ?_⟩ <;> simp only [List.length_cons] <;> push_cast <;> omega
    · have ho' : Bd (k + 1) (addP o (vecOf 2 d)) := by
        refine ⟨by simp [h0], ?_⟩
        rw [getD_addP _ _ _ (by omega) (by simp), getD_addP _ _ _ (by omega) (by simp), getD_vecOf 2 d 0 (by omega),
          getD_vecOf 2 d 1 (by omega)]
        split_ifs <;> push_cast <;> omega
      have := bd_walkPts _ ds (k + 1) ho' p hp
      simp only [List.length_cons]
      rwa [show k + 1 + ds.length = k + (ds.length + 1) by omega] at this

/-- A point in the bounding box of bounded points is bounded. -/
theorem bd_of_inBB {m : ℕ} {pts : List (List ℤ)} (hpts : ∀ p ∈ pts, Bd m p) {x : List ℤ}
    (hx : inBB 2 pts x = true) : Bd m x := by
  simp only [inBB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, List.any_eq_true,
    decide_eq_true_eq] at hx
  obtain ⟨hlen, hcoord⟩ := hx
  obtain ⟨⟨p0, hp0, e0⟩, ⟨q0, hq0, f0⟩⟩ := hcoord 0 (by norm_num)
  obtain ⟨⟨p1, hp1, e1⟩, ⟨q1, hq1, f1⟩⟩ := hcoord 1 (by norm_num)
  obtain ⟨-, a1, -, -, -⟩ := hpts p0 hp0
  obtain ⟨-, -, b2, -, -⟩ := hpts q0 hq0
  obtain ⟨-, -, -, c3, -⟩ := hpts p1 hp1
  obtain ⟨-, -, -, -, d4⟩ := hpts q1 hq1
  exact ⟨hlen, by omega, by omega, by omega, by omega⟩

/-- `torPt v` is injective on points bounded by `m` when `2m < L`. -/
theorem torPt_inj {v : TorV L} {m : ℕ} (hm : 2 * m < L) {q q' : List ℤ} (hq : Bd m q) (hq' : Bd m q')
    (h : torPt v q = torPt v q') : q = q' := by
  have h1 := congrArg (fun u : TorV L => (((u.1 : ℕ) : ℤ))) h
  have h2 := congrArg (fun u : TorV L => (((u.2 : ℕ) : ℤ))) h
  simp only [torPt_fst, torPt_snd] at h1 h2
  have hv1 := v.1.2
  have hv2 := v.2.2
  obtain ⟨l, a1, a2, a3, a4⟩ := hq
  obtain ⟨l', b1, b2, b3, b4⟩ := hq'
  rw [emod_cases (by omega) (by omega), emod_cases (by omega) (by omega)] at h1 h2
  have e0 : q.getD 0 0 = q'.getD 0 0 := by split_ifs at h1 <;> omega
  have e1 : q.getD 1 0 = q'.getD 1 0 := by split_ifs at h2 <;> omega
  rw [list_two_eq l, list_two_eq l', e0, e1]

/-- The torus edge of a relative edge, translated by `v`. -/
def torE (v : TorV L) (e : Edge) : Sym2 (Vx (TorV L)) := s(Vx.det (torPt v e.1), Vx.det (torPt v e.2))

/-- The ends of the edges of a list are bounded by `m`. -/
def BdE (m : ℕ) (Ls : List Edge) : Prop := ∀ e ∈ Ls, Bd m e.1 ∧ Bd m e.2

theorem ldeg_map_torE (v : TorV L) {m : ℕ} (hm : 2 * m < L) {Ls : List Edge} (hLs : BdE m Ls) {q : List ℤ}
    (hq : Bd m q) : ldeg (Ls.map (torE v)) (Vx.det (torPt v q)) = degC Ls q := by
  unfold ldeg degC
  rw [List.countP_map]
  apply List.countP_congr
  intro e he
  obtain ⟨h1, h2⟩ := hLs e he
  simp only [Function.comp, torE, Sym2.mem_iff, Vx.det.injEq, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl (torPt_inj hm h1 hq h.symm)
    · exact Or.inr (torPt_inj hm h2 hq h.symm)
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

theorem ldeg_map_torE_zero (v : TorV L) {m : ℕ} {Ls : List Edge} (hLs : BdE m Ls) {u : TorV L}
    (hu : ∀ q, Bd m q → torPt v q ≠ u) : ldeg (Ls.map (torE v)) (Vx.det u) = 0 := by
  unfold ldeg
  rw [List.countP_eq_zero]
  intro e he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  obtain ⟨h1, h2⟩ := hLs f hf
  simp only [torE, Sym2.mem_iff, Vx.det.injEq, decide_eq_true_eq, not_or]
  exact ⟨fun h => hu _ h1 h.symm, fun h => hu _ h2 h.symm⟩

/-- Equal degree parities of bounded relative edge lists give equal odd vertices on the torus. -/
theorem oddD_map_torE (v : TorV L) {m : ℕ} (hm : 2 * m < L) {A B : List Edge} (hA : BdE m A) (hB : BdE m B)
    (hpar : parOK A B = true) : oddD (A.map (torE v)) = oddD (B.map (torE v)) := by
  ext u
  simp only [oddD, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hu : ∃ q, Bd m q ∧ torPt v q = u
  · obtain ⟨q, hq, rfl⟩ := hu
    rw [ldeg_map_torE v hm hA hq, ldeg_map_torE v hm hB hq, Nat.odd_iff, Nat.odd_iff, parOK_spec hpar]
  · simp only [not_exists, not_and] at hu
    rw [ldeg_map_torE_zero v hA hu, ldeg_map_torE_zero v hB hu]

theorem torE_inj_same {v : TorV L} {m : ℕ} (hm : 2 * m < L) {e f : Edge} (he : Bd m e.1 ∧ Bd m e.2)
    (hf : Bd m f.1 ∧ Bd m f.2) (h : torE v e = torE v f) : sameE e f = true := by
  simp only [torE, Sym2.eq_iff, Vx.det.injEq] at h
  simp only [sameE, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨torPt_inj hm he.1 hf.1 h1, torPt_inj hm he.2 hf.2 h2⟩
  · exact Or.inr ⟨torPt_inj hm he.1 hf.2 h1, torPt_inj hm he.2 hf.1 h2⟩

theorem nodup_map_torE (v : TorV L) {m : ℕ} (hm : 2 * m < L) :
    ∀ {Ls : List Edge}, BdE m Ls → nodupE Ls = true → (Ls.map (torE v)).Nodup
  | [], _, _ => List.nodup_nil
  | e :: Ls, hLs, h => by
    simp only [nodupE, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, nodup_map_torE v hm (fun f hf => hLs f (List.mem_cons_of_mem _ hf)) h.2⟩
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hmem
    have := torE_inj_same hm (hLs e (by simp)) (hLs f (List.mem_cons_of_mem _ hf)) hfe.symm
    rw [h.1 f hf] at this
    exact absurd this (by simp)

/-! ## `Φ` on the torus -/

theorem qoff_eq (v : TorV L) :
    qoff v = if 2 * ((v.1 : ℕ) : ℤ) < L then ((v.1 : ℕ) : ℤ) else ((v.1 : ℕ) : ℤ) - L := by
  have := v.1.2
  unfold qoff qoffZ
  rw [Int.emod_eq_of_lt (by omega) (by omega)]

/-- The column of `torPt v q` is `L·A + B` for `(A, B) = phiT (qoff v + q.x)`. -/
theorem xcol_torPt (v : TorV L) {M : ℕ} (hML : 2 * M < L) {q : List ℤ} (h0 : -(M : ℤ) ≤ q.getD 0 0)
    (h1 : q.getD 0 0 ≤ M) :
    xcol (Vx.det (torPt v q)) = L * (phiT (qoff v + q.getD 0 0)).1 + (phiT (qoff v + q.getD 0 0)).2 := by
  have hv := v.1.2
  simp only [xcol]
  rw [torPt_fst, qoff_eq, emod_cases (by omega) (by omega)]
  unfold phiT
  split_ifs <;> simp only [mul_zero, mul_one, zero_add] <;> omega

theorem phi_torE (v : TorV L) {M : ℕ} (hML : 2 * M < L) {e : Edge} (he : Bd M e.1 ∧ Bd M e.2) :
    phiTor L (torE v e) =
      L * (addPair (phiT (qoff v + e.1.getD 0 0)) (phiT (qoff v + e.2.getD 0 0))).1 +
        (addPair (phiT (qoff v + e.1.getD 0 0)) (phiT (qoff v + e.2.getD 0 0))).2 := by
  simp only [torE, phiTor, Sym2.lift_mk, addPair]
  rw [xcol_torPt v hML he.1.2.1 he.1.2.2.1, xcol_torPt v hML he.2.2.1 he.2.2.2.1]
  ring

/-- `Φ` of the torus image of a bounded relative edge list is `L·A + B` for its `phiTE`. -/
theorem phi_map_torE (v : TorV L) {M : ℕ} (hML : 2 * M < L) :
    ∀ {Ls : List Edge}, BdE M Ls →
      ((Ls.map (torE v)).map (phiTor L)).sum = L * (phiTE (qoff v) Ls).1 + (phiTE (qoff v) Ls).2
  | [], _ => by simp [phiTE]
  | e :: Ls, h => by
    simp only [List.map_cons, List.sum_cons, phiTE]
    rw [phi_torE v hML (h e (by simp)), phi_map_torE v hML (fun f hf => h f (List.mem_cons_of_mem _ hf))]
    simp only [addPair]
    ring

theorem lexLt_iff (a b : ℤ × ℤ) : lexLt a b = true ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
  simp [lexLt]

/-! ## Windows of torus paths -/

theorem ledges_map_detT {V : Type*} : ∀ ws : List V,
    ledges (ws.map Vx.det) = (pairs ws).map (fun uv => s(Vx.det uv.1, Vx.det uv.2))
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by
    simp only [List.map_cons, ledges_cons_cons, pairs, List.cons.injEq, true_and]
    exact ledges_map_detT (v :: rest)

theorem rel_of_mem_pairs {α : Type*} {R : α → α → Prop} :
    ∀ {ws : List α} {u v : α}, ws.IsChain R → (u, v) ∈ pairs ws → R u v
  | [], _, _, _, h => by simp [pairs] at h
  | [_], _, _, _, h => by simp [pairs] at h
  | a :: b :: rest, u, v, hc, h => by
    rw [List.isChain_cons_cons] at hc
    simp only [pairs, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact hc.1
    · exact rel_of_mem_pairs hc.2 h

theorem length_edgesFrom (n : ℕ) : ∀ (o : List ℤ) (w : List (ℕ × Bool)), (edgesFrom n o w).length = w.length
  | _, [] => rfl
  | o, (d, l) :: w => by simp [edgesFrom, length_edgesFrom n _ w]

theorem length_patOfT (S : Finset (Sym2 (Vx (TorV L)))) :
    ∀ vs : List (TorV L), (patOfT S vs).length = vs.length - 1
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by simp [patOfT, length_patOfT S (v :: rest)]

theorem patOfT_drop (S : Finset (Sym2 (Vx (TorV L)))) :
    ∀ (vs : List (TorV L)) (i : ℕ), (patOfT S vs).drop i = patOfT S (vs.drop i)
  | _, 0 => rfl
  | [], _ + 1 => by simp [patOfT]
  | [_], _ + 1 => by simp [patOfT]
  | u :: v :: rest, i + 1 => by
    simp only [patOfT, List.drop_succ_cons]
    exact patOfT_drop S (v :: rest) i

theorem patOfT_take (S : Finset (Sym2 (Vx (TorV L)))) :
    ∀ (vs : List (TorV L)) (m : ℕ), (patOfT S vs).take m = patOfT S (vs.take (m + 1))
  | [], _ => by simp [patOfT]
  | [_], _ => by simp [patOfT]
  | u :: v :: rest, 0 => by simp [patOfT]
  | u :: v :: rest, m + 1 => by
    simp only [patOfT, List.take_succ_cons]
    rw [patOfT_take S (v :: rest) m, List.take_succ_cons]

/-- The labelled edges of the pattern of a torus path, from a relative point `p` at its first vertex, mapped to the
torus, are the labelled edges of the path. -/
theorem edgesFrom_patOfT (v0 : TorV L) (S : Finset (Sym2 (Vx (TorV L)))) :
    ∀ (p : List ℤ) (ws : List (TorV L)) (u : TorV L), p.length = 2 → torPt v0 p = u →
      (u :: ws).IsChain (fun a b => TorStep a b ∨ TorStep b a) →
      (edgesFrom 2 p (patOfT S (u :: ws))).map (fun e => (torE v0 e.1, e.2)) =
        (pairs (u :: ws)).map (fun uv => (s(Vx.det uv.1, Vx.det uv.2), decide (s(Vx.det uv.1, Vx.det uv.2) ∉ S)))
  | p, [], u, _, _, _ => by simp [patOfT, edgesFrom, pairs]
  | p, w :: ws, u, hp, hu, hc => by
    rw [List.isChain_cons_cons] at hc
    have hu' : torPt v0 (addP p (vecOf 2 (torDir u w))) = w := by
      rw [← torPt_add v0 hp (by simp), hu, torPt_torDir hc.1]
    simp only [patOfT, edgesFrom, pairs, List.map_cons, List.cons.injEq]
    refine ⟨?_, edgesFrom_patOfT v0 S _ ws w (by simp [hp]) hu' hc.2⟩
    simp only [torE, hu, hu']

/-- **Soundness of the seam exclusions for a torus path** (the whole path is the window). -/
theorem tor_not_exclT {L0 : ℕ} (hL0 : L0 ≤ L) {E C : Finset (Sym2 (Vx (TorV L)))} (hE : E ⊆ torEdges L)
    (hC : IsPhiMinFailT (phiTor L) E C) (v0 : TorV L) (rest : List (TorV L)) (hnd : (v0 :: rest).Nodup)
    (hch : ((v0 :: rest).map Vx.det).IsChain (decGraph (C ∆ E)).Adj) (hlen : 2 * rest.length + 2 < L) :
    ¬ ExclT L0 (qoff v0) (patOfT E (v0 :: rest)) := by
  rintro ⟨W, hW⟩
  set ws := v0 :: rest with hws
  set w := patOfT E ws with hw
  set m := rest.length with hm
  have hm2 : 2 * m < L := by omega
  have hL3 : 3 ≤ L := by omega
  have hCg : C ⊆ torEdges L := hC.1.1
  have hRg : ∀ e ∈ C ∆ E, e ∈ torEdges L := by
    intro e he
    rcases Finset.mem_symmDiff.mp he with ⟨h, -⟩ | ⟨h, -⟩
    · exact hCg h
    · exact hE h
  -- consecutive vertices are torus neighbours, joined by edges of the residual
  have hchR : ws.IsChain (fun a b => s(Vx.det a, Vx.det b) ∈ C ∆ E) := by
    rw [List.isChain_map] at hch
    exact hch.imp (fun a b h => h.2)
  have hchT : ws.IsChain (fun a b => TorStep a b ∨ TorStep b a) :=
    hchR.imp (fun a b h => mem_torEdges.mp (hRg _ h))
  have hlenw : w.length = m := by rw [hw, length_patOfT]; simp [hws, hm]
  set pts := walkPts 2 (zeros 2) (w.map Prod.fst) with hpts
  have hptsBd : ∀ p ∈ pts, Bd m p := by
    intro p hp
    have := bd_walkPts (zeros 2) (w.map Prod.fst) 0 bd_zeros p hp
    simpa [hlenw] using this
  -- the labelled window edges
  set WE := (pairs ws).map (fun uv => (s(Vx.det uv.1, Vx.det uv.2), decide (s(Vx.det uv.1, Vx.det uv.2) ∉ E)))
    with hWE
  have hE0 : (edgesFrom 2 (zeros 2) w).map (fun e => (torE v0 e.1, e.2)) = WE :=
    edgesFrom_patOfT v0 E (zeros 2) rest v0 (by simp) (torPt_zeros v0) hchT
  have hwin : ∀ e ∈ edgesFrom 2 (zeros 2) w, (Bd m e.1.1 ∧ Bd m e.1.2) ∧ torE v0 e.1 ∈ torEdges L ∧
      (e.2 = true → torE v0 e.1 ∈ C) ∧ (e.2 = false → torE v0 e.1 ∉ C) := by
    intro e he
    have hpe := mem_edgesFrom_pts 2 (zeros 2) w e he
    refine ⟨⟨hptsBd _ hpe.1, hptsBd _ hpe.2⟩, ?_⟩
    have hmem : (torE v0 e.1, e.2) ∈ WE := by
      rw [← hE0]; exact List.mem_map_of_mem (f := fun e => (torE v0 e.1, e.2)) he
    rw [hWE, List.mem_map] at hmem
    obtain ⟨uv, huv, heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨he1, he2⟩ := heq
    rw [← he1]
    have hR : s(Vx.det uv.1, Vx.det uv.2) ∈ C ∆ E := rel_of_mem_pairs hchR huv
    refine ⟨hRg _ hR, ?_, ?_⟩
    · intro hl
      rw [hl] at he2
      have hnE : s(Vx.det uv.1, Vx.det uv.2) ∉ E := by simpa using he2
      rcases Finset.mem_symmDiff.mp hR with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hnE
    · intro hl
      rw [hl] at he2
      have hE' : s(Vx.det uv.1, Vx.det uv.2) ∈ E := by simpa using he2
      rcases Finset.mem_symmDiff.mp hR with ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd hE' h
      · exact h
  -- the window edges are distinct
  have hperm : (cEdges 2 w ++ eEdges 2 w).Perm ((edgesFrom 2 (zeros 2) w).map Prod.fst) := by
    unfold cEdges eEdges
    rw [← List.map_append]
    exact (List.filter_append_perm _ _).map _
  have hall : ((cEdges 2 w ++ eEdges 2 w).map (torE v0)).Nodup := by
    have hl : ((edgesFrom 2 (zeros 2) w).map Prod.fst).map (torE v0) = ledges (ws.map Vx.det) := by
      rw [ledges_map_detT, List.map_map]
      have := congrArg (List.map Prod.fst) hE0
      rw [List.map_map, hWE, List.map_map] at this
      exact this
    rw [(hperm.map _).nodup_iff, hl]
    exact ledges_nodup (hnd.map (fun _ _ h => Vx.det.inj h))
  have hCElen : (cEdges 2 w).length + (eEdges 2 w).length = m := by
    rw [← List.length_append, hperm.length_eq, List.length_map, length_edgesFrom, hlenw]
  -- unpack the witness check
  simp only [checkWT, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hW
  obtain ⟨⟨halt, hpar⟩, hsz⟩ := hW
  set X := cEdges 2 w with hX
  set Y := if W.useE then eEdges 2 w else [] with hY
  set P := altEdges 2 W.alt with hP
  have hXmem : ∀ e ∈ X, ∃ e' ∈ edgesFrom 2 (zeros 2) w, e'.2 = true ∧ e'.1 = e := by
    intro e he
    simp only [hX, cEdges, List.mem_map, List.mem_filter] at he
    obtain ⟨e', ⟨he', hl⟩, rfl⟩ := he
    exact ⟨e', he', hl, rfl⟩
  have hYmem : ∀ e ∈ Y, ∃ e' ∈ edgesFrom 2 (zeros 2) w, e'.2 = false ∧ e'.1 = e := by
    intro e he
    rw [hY] at he
    split_ifs at he
    · simp only [eEdges, List.mem_map, List.mem_filter, Bool.not_eq_true'] at he
      obtain ⟨e', ⟨he', hl⟩, rfl⟩ := he
      exact ⟨e', he', hl, rfl⟩
    · simp at he
  have hYlen : Y.length ≤ (eEdges 2 w).length := by
    rw [hY]; split_ifs
    · exact le_refl _
    · simp
  have hgoodX : BdE m X := by
    intro e he
    obtain ⟨e', he', -, rfl⟩ := hXmem e he
    exact (hwin e' he').1
  have hgoodY : BdE m Y := by
    intro e he
    obtain ⟨e', he', -, rfl⟩ := hYmem e he
    exact (hwin e' he').1
  have hgoodP : BdE m P := by
    intro e he
    simp only [hP, altEdges, List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨⟨-, h1⟩, h2⟩ := halt x hx
    exact ⟨bd_of_inBB hptsBd h1, bd_of_inBB hptsBd h2⟩
  have hgoodXY : BdE m (X ++ Y) := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact hgoodX e h
    · exact hgoodY e h
  -- the hypotheses of the exchange lemma
  have hXYnd : (X.map (torE v0) ++ Y.map (torE v0)).Nodup := by
    rw [hY]
    split_ifs
    · rw [← List.map_append]; exact hall
    · rw [List.map_nil, List.append_nil, ← List.append_nil (X.map (torE v0))]
      rw [List.map_append] at hall
      exact (List.nodup_append.mp hall).1.append List.nodup_nil (by simp)
  have hXC : ∀ e ∈ X.map (torE v0), e ∈ C := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    obtain ⟨e', he', hl, rfl⟩ := hXmem f hf
    exact (hwin e' he').2.2.1 hl
  have hYC : ∀ e ∈ Y.map (torE v0), e ∉ C := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    obtain ⟨e', he', hl, rfl⟩ := hYmem f hf
    exact (hwin e' he').2.2.2 hl
  have hPg : ∀ e ∈ P.map (torE v0), e ∈ torEdges L := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    simp only [hP, altEdges, List.mem_map] at hf
    obtain ⟨x, hx, rfl⟩ := hf
    obtain ⟨⟨hd, h1⟩, -⟩ := halt x hx
    have b1 := bd_of_inBB hptsBd h1
    simp only [torE]
    rw [← torPt_add v0 b1.1 (by simp)]
    exact step_mem_torEdges _ hd
  have hg : ∀ e ∈ X.map (torE v0) ++ Y.map (torE v0) ++ P.map (torE v0), e ∈ torEdges L := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · rcases List.mem_append.mp h with h' | h'
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h'
        obtain ⟨e', he', -, rfl⟩ := hXmem f hf
        exact (hwin e' he').2.1
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h'
        obtain ⟨e', he', -, rfl⟩ := hYmem f hf
        exact (hwin e' he').2.1
    · exact hPg e h
  have hodd : oddD (P.map (torE v0)) = oddD (X.map (torE v0) ++ Y.map (torE v0)) := by
    rw [← List.map_append]
    exact oddD_map_torE v0 hm2 hgoodP hgoodXY hpar
  have hPlen : P.length ≤ X.length := by
    rcases hsz with h | ⟨⟨⟨h, -⟩, -⟩, -⟩ <;> omega
  have hshort : (X.map (torE v0)).length + (Y.map (torE v0)).length + (P.map (torE v0)).length < L := by
    simp only [List.length_map]
    omega
  have hex := exchangeT hL3 hC hXYnd hXC hYC hg hshort hodd
  simp only [List.length_map] at hex
  rcases hsz with hlt | ⟨⟨⟨heq, hnodup⟩, hlex⟩, habs⟩
  · exact absurd hex.1 (by omega)
  · have h2 := hex.2 heq.symm (nodup_map_torE v0 hm2 hgoodP hnodup)
    rw [phi_map_torE v0 hm2 hgoodX, phi_map_torE v0 hm2 hgoodY, phi_map_torE v0 hm2 hgoodP] at h2
    rw [lexLt_iff] at hlex
    simp only [addPair] at hlex habs
    have hB : (phiTE (qoff v0) Y).2 + (phiTE (qoff v0) P).2 - (phiTE (qoff v0) X).2 < L := by omega
    rcases hlex with hA | ⟨hA, hB'⟩
    · nlinarith [mul_le_mul_of_nonneg_left (show (phiTE (qoff v0) Y).1 + (phiTE (qoff v0) P).1 + 1 ≤
        (phiTE (qoff v0) X).1 by omega) (show (0 : ℤ) ≤ L by positivity)]
    · have hmul : (L : ℤ) * (phiTE (qoff v0) X).1 = L * (phiTE (qoff v0) Y).1 + L * (phiTE (qoff v0) P).1 := by
        rw [← hA]; ring
      linarith

/-- **Soundness of the seam exclusions on the torus**: no window of `2..M` edges of a self-avoiding path in the
residual of a failing minimum-weight correction of least `Φ` is excluded at the seam offset of its first vertex. -/
theorem tor_window_not_excl {L L0 M : ℕ} (hL0 : L0 ≤ L) (hML : 2 * M + 2 < L)
    {E C : Finset (Sym2 (Vx (TorV L)))} (hE : E ⊆ torEdges L) (hC : IsPhiMinFailT (phiTor L) E C)
    {vs : List (TorV L)} (hnd : vs.Nodup) (hch : (vs.map Vx.det).IsChain (decGraph (C ∆ E)).Adj)
    {i m : ℕ} (hm2 : 2 ≤ m) (hmM : m ≤ M) (him : i + m < vs.length) :
    ¬ ExclT L0 (qoff (vs[i]'(by omega))) (((patOfT E vs).drop i).take m) := by
  have hi : i < vs.length := by omega
  have hws : (vs.drop i).take (m + 1) = vs[i] :: (vs.drop (i + 1)).take m := by
    rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]
  have hnd' : ((vs.drop i).take (m + 1)).Nodup :=
    hnd.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  have hch' : (((vs.drop i).take (m + 1)).map Vx.det).IsChain (decGraph (C ∆ E)).Adj := by
    rw [List.map_take, List.map_drop]
    exact (hch.drop i).take (m + 1)
  rw [hws] at hnd' hch'
  rw [patOfT_drop, patOfT_take, hws]
  refine tor_not_exclT hL0 hE hC _ _ hnd' hch' ?_
  simp only [List.length_take, List.length_drop]
  omega

end QEC
