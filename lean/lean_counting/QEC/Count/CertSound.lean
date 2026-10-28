import QEC.Count.Defs
import QEC.Count.Geom
import Mathlib.Algebra.BigOperators.Field

/-!
# Soundness of the certificate checks

For a certificate (`Params`, sorted keys, potentials `Hs`): the listed states `IsSt`, the potential `Hof` (`0` off the
list), and the real weights `ω_E = wE / Q`, `ω_C = wC / Q`, `λ = lamN / lamD`. From the checks of the computational
core (`rowCheck` for every listed state, `dfsOK`, `startOK`) we get the hypotheses of `sum_legal_le`:

* `cert_pos`: `0 < Hmin ≤ H(s)` on the listed states;
* `cert_start`: every legal walk of `K` steps is listed (from `dfsOK`);
* `cert_closed`: every legal successor of a listed state leads to a listed state;
* `cert_rows`: the rows `∑_{x successor} ω(x) H(next) ≤ λ H(s)`;
* `cert_startSum`: `(ω_E + ω_C)² ∑_{s listed} ω(s) H(s) / Hmin ≤ K0n / K0d`.

A witness found by the search is used only after `checkW` accepted it, so `exclWin P u = true` gives `Excl` (an
exclusion is never certified by the search itself). A listed key is only used through the checked equality
`keys[j] = key`.
-/

namespace QEC

open Finset QECComp

variable (P : Params) (keys Hs : Array ℕ)

/-- The listed states. -/
def IsSt (s : List (ℕ × Bool)) : Prop :=
  s.length = P.K ∧ DirOK P.n s ∧ (lookup keys (keyOf P.n s)).isSome = true

/-- The potential: `H` of a listed state, `0` off the list. -/
def Hof (s : List (ℕ × Bool)) : ℕ :=
  match lookup keys (keyOf P.n s) with
  | some j => Hs[j]!
  | none => 0

/-- The weight of an E-edge. -/
noncomputable def ωEof : ℝ := (P.wE : ℝ) / P.Q

/-- The weight of a C-edge. -/
noncomputable def ωCof : ℝ := (P.wC : ℝ) / P.Q

/-- The row factor. -/
noncomputable def lamOf : ℝ := (P.lamN : ℝ) / P.lamD

namespace CertSound

/-! ## Helpers about the computational core -/

theorem lookup_some {keys : Array ℕ} {k j : ℕ} (h : lookup keys k = some j) : j < keys.size ∧ keys[j]! = k := by
  unfold lookup at h
  simp only at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    exact hc
  · exact absurd h (by simp)

theorem nodupPts_iff : ∀ (l : List (List ℤ)), nodupPts l = true ↔ l.Nodup
  | [] => by simp [nodupPts]
  | x :: xs => by
    simp only [nodupPts, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons, nodupPts_iff xs]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun hm => ?_, h2⟩
      have : xs.contains x = true := List.contains_iff_mem.mpr hm
      rw [h1] at this
      exact absurd this (by simp)
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      cases hc : xs.contains x
      · rfl
      · exact absurd (List.contains_iff_mem.mp hc) h1

theorem mem_candList {n : ℕ} {x : ℕ × Bool} : x ∈ candList n ↔ x.1 < 2 * n := by
  obtain ⟨d, b⟩ := x
  simp only [candList, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq]
  constructor
  · rintro ⟨d', hd', h⟩
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact hd'
  · intro hd
    refine ⟨d, hd, ?_⟩
    cases b <;> simp

theorem candList_nodup (n : ℕ) : (candList n).Nodup := by
  unfold candList
  rw [List.nodup_flatMap]
  refine ⟨fun d _ => by simp, ?_⟩
  refine List.Pairwise.imp ?_ (List.nodup_range)
  intro a b hab
  rw [Function.onFun, List.disjoint_left]
  intro x hx hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with h | h <;> simp_all

theorem mem_cands {n : ℕ} {x : ℕ × Bool} : x ∈ cands n ↔ x.1 < 2 * n := by
  simp [cands]

theorem cands_eq_toFinset (n : ℕ) : cands n = (candList n).toFinset := by
  ext x
  rw [mem_cands, List.mem_toFinset, mem_candList]

theorem digit_lt {n : ℕ} {x : ℕ × Bool} (hx : x.1 < 2 * n) : digit x < 4 * n := by
  unfold digit
  split <;> omega

theorem keyOf_append (n : ℕ) (w : List (ℕ × Bool)) (x : ℕ × Bool) :
    keyOf n (w ++ [x]) = keyOf n w * (4 * n) + digit x := by
  simp [keyOf, List.foldl_append]

theorem length_decodeKey (n : ℕ) : ∀ (K k : ℕ), (decodeKey n K k).length = K
  | 0, _ => rfl
  | K + 1, k => by simp [decodeKey, length_decodeKey n K]

/-- Keys decode to their patterns. -/
theorem decodeKey_keyOf {n : ℕ} (hn : 0 < n) : ∀ (K : ℕ) (s : List (ℕ × Bool)), s.length = K → DirOK n s →
    decodeKey n K (keyOf n s) = s
  | 0, s, hs, _ => by
    rw [List.length_eq_zero_iff] at hs
    subst hs
    rfl
  | K + 1, s, hs, hd => by
    obtain ⟨s', x, rfl⟩ : ∃ s' x, s = s' ++ [x] := by
      have hne : s ≠ [] := by rintro rfl; simp at hs
      exact ⟨s.dropLast, s.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hs' : s'.length = K := by simp at hs; omega
    have hd' : DirOK n s' := fun y hy => hd y (List.mem_append_left _ hy)
    have hx : x.1 < 2 * n := hd x (by simp)
    have hdig := digit_lt hx
    have hB : 0 < 4 * n := by omega
    rw [keyOf_append]
    simp only [decodeKey]
    have e1 : (keyOf n s' * (4 * n) + digit x) / (4 * n) = keyOf n s' := by
      rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hdig, Nat.add_zero]
    have e2 : (keyOf n s' * (4 * n) + digit x) % (4 * n) = digit x := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hdig]
    rw [e1, e2, decodeKey_keyOf hn K s' hs' hd']
    obtain ⟨d, b⟩ := x
    cases b
    · simp [digit]
    · simp [digit]
      omega

/-- The key is injective on the patterns of `K` valid steps. -/
theorem keyOf_inj {n K : ℕ} (hn : 0 < n) {s t : List (ℕ × Bool)} (hs : s.length = K) (ht : t.length = K)
    (hds : DirOK n s) (hdt : DirOK n t) (h : keyOf n s = keyOf n t) : s = t := by
  rw [← decodeKey_keyOf hn K s hs hds, ← decodeKey_keyOf hn K t ht hdt, h]

/-- The directions of a decoded key are valid. -/
theorem dirOK_decodeKey {n : ℕ} (hn : 0 < n) : ∀ (K k : ℕ), DirOK n (decodeKey n K k)
  | 0, _ => by simp [DirOK, decodeKey]
  | K + 1, k => by
    intro y hy
    simp only [decodeKey, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact dirOK_decodeKey hn K _ y hy
    · have : k % (4 * n) < 4 * n := Nat.mod_lt _ (by omega)
      show k % (4 * n) / 2 < 2 * n
      omega

/-! ## Folds that stay `some` -/

theorem foldl_none {α : Type*} (f : Option ℕ → α → Option ℕ) (hnone : ∀ x, f none x = none) :
    ∀ L : List α, L.foldl f none = none
  | [] => rfl
  | x :: L => by simp only [List.foldl, hnone, foldl_none f hnone L]

/-- A fold that adds `g x` for the good `x` and fails at a bad one: its result is the sum, and every element is
good. -/
theorem foldl_opt {α : Type*} (f : Option ℕ → α → Option ℕ) (g : α → ℕ) (good : α → Prop)
    (hnone : ∀ x, f none x = none) (hgood : ∀ a x, good x → f (some a) x = some (a + g x))
    (hbad : ∀ a x, ¬ good x → f (some a) x = none) :
    ∀ (L : List α) (a t : ℕ), L.foldl f (some a) = some t → t = a + (L.map g).sum ∧ ∀ x ∈ L, good x
  | [], a, t, h => by
    simp only [List.foldl, Option.some.injEq] at h
    simp [h]
  | x :: L, a, t, h => by
    simp only [List.foldl] at h
    by_cases hx : good x
    · rw [hgood a x hx] at h
      obtain ⟨h1, h2⟩ := foldl_opt f g good hnone hgood hbad L (a + g x) t h
      refine ⟨by rw [h1, List.map_cons, List.sum_cons]; omega, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact h2 y hy
    · rw [hbad a x hx, foldl_none f hnone] at h
      exact absurd h (by simp)

/-! ## The witness check, unfolded; single-edge windows are never excluded -/

/-- What an accepted witness gives. -/
theorem checkW_spec {n : ℕ} {c : List ℤ} {w : List (ℕ × Bool)} {W : Wit} (h : checkW n c w W = true) :
    (∀ a ∈ W.alt, a.2 < 2 * n ∧ inBB n (walkPts n (zeros n) (w.map Prod.fst)) a.1 = true ∧
      inBB n (walkPts n (zeros n) (w.map Prod.fst)) (addP a.1 (vecOf n a.2)) = true) ∧
    parOK (altEdges n W.alt) (cEdges n w ++ (if W.useE then eEdges n w else [])) = true ∧
    ((if W.useE then eEdges n w else []).length + (altEdges n W.alt).length < (cEdges n w).length ∨
      ((if W.useE then eEdges n w else []).length + (altEdges n W.alt).length = (cEdges n w).length ∧
        nodupE (altEdges n W.alt) = true ∧
        phiE c (if W.useE then eEdges n w else []) + phiE c (altEdges n W.alt) < phiE c (cEdges n w))) := by
  unfold checkW at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨fun a ha => ⟨(h1 a ha).1.1, (h1 a ha).1.2, (h1 a ha).2⟩, h2, by
    rcases h3 with h3 | ⟨⟨h3, h4⟩, h5⟩
    · exact Or.inl h3
    · exact Or.inr ⟨h3, h4, h5⟩⟩

theorem vecOf_ne_zeros {n d : ℕ} (hd : d < 2 * n) : vecOf n d ≠ zeros n := by
  intro h
  have h2 : (vecOf n d)[d / 2]? = (zeros n)[d / 2]? := by rw [h]
  have hi : d / 2 < n := by omega
  simp only [vecOf, zeros, List.getElem?_map, List.getElem?_range hi, List.getElem?_replicate, hi, ite_true,
    Option.map_some] at h2
  split at h2 <;> simp at h2

theorem degC_single (e : Edge) (y : List ℤ) : degC [e] y = if (e.1 == y || e.2 == y) = true then 1 else 0 := by
  simp only [degC, List.countP_cons, List.countP_nil, zero_add]

theorem cEdges_single (n : ℕ) (x : ℕ × Bool) :
    cEdges n [x] = if x.2 then [(zeros n, addP (zeros n) (vecOf n x.1))] else [] := by
  obtain ⟨d, b⟩ := x
  cases b <;> simp [cEdges, edgesFrom]

theorem eEdges_single (n : ℕ) (x : ℕ × Bool) :
    eEdges n [x] = if x.2 then [] else [(zeros n, addP (zeros n) (vecOf n x.1))] := by
  obtain ⟨d, b⟩ := x
  cases b <;> simp [eEdges, edgesFrom]

/-- A window of one edge is never excluded. -/
theorem not_excl_single {n : ℕ} {c : List ℤ} {x : ℕ × Bool} (hx : x.1 < 2 * n) : ¬ Excl n c [x] := by
  rintro ⟨W, hW⟩
  obtain ⟨-, hpar, hsz⟩ := checkW_spec hW
  rw [cEdges_single, eEdges_single] at hpar hsz
  obtain ⟨d, b⟩ := x
  cases b
  · -- an E-edge: there are no C-edges
    simp only [Bool.false_eq_true, ite_false, List.length_nil] at hsz
    rcases hsz with h | ⟨h1, -, h3⟩
    · omega
    · cases hU : W.useE <;> simp only [hU, ite_true, List.length_cons, List.length_nil] at h1
      · have hP : altEdges n W.alt = [] := List.length_eq_zero_iff.mp (by omega)
        simp [hU, hP, phiE] at h3
      · omega
  · -- a C-edge: the alternative must be the same edge
    simp only [ite_true] at hpar hsz
    set e : Edge := (zeros n, addP (zeros n) (vecOf n d)) with he
    have hne : e.1 ≠ e.2 := by
      simp only [he]
      rw [show addP (zeros n) (vecOf n d) = vecOf n d by
        have := zeros_addP (vecOf n d); rwa [length_vecOf] at this]
      exact fun h => vecOf_ne_zeros hx h.symm
    have hY : (if W.useE then ([] : List Edge) else []) = [] := by split <;> rfl
    rw [hY, List.append_nil] at hpar
    rw [hY] at hsz
    simp only [List.length_nil, zero_add, List.length_cons] at hsz
    unfold parOK at hpar
    rw [List.all_eq_true] at hpar
    have hpe := hpar e (by simp)
    simp only [Bool.and_eq_true, beq_iff_eq, degC_single, beq_self_eq_true, Bool.true_or, ite_true,
      Bool.or_true] at hpe
    obtain ⟨hp1, hp2⟩ := hpe
    rcases hsz with h | ⟨h1, -, h3⟩
    · have hP : altEdges n W.alt = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hP] at hp1
      simp [degC] at hp1
    · obtain ⟨f, hf⟩ := List.length_eq_one_iff.mp h1
      rw [hf] at hp1 hp2 h3
      rw [degC_single] at hp1 hp2
      have hf1 : (f.1 == e.1 || f.2 == e.1) = true := by
        by_contra hc
        simp only [Bool.not_eq_true] at hc
        simp [hc] at hp1
      have hf2 : (f.1 == e.2 || f.2 == e.2) = true := by
        by_contra hc
        simp only [Bool.not_eq_true] at hc
        simp [hc] at hp2
      simp only [Bool.or_eq_true, beq_iff_eq] at hf1 hf2
      have hphi : phiE c [f] = phiE c [e] := by
        simp only [phiE, add_zero]
        rcases hf1 with h | h <;> rcases hf2 with h' | h'
        · exact absurd (h.symm.trans h') hne
        · rw [h, h']
        · rw [h, h', add_comm]
        · exact absurd (h.symm.trans h') hne
      simp only [phiE, add_zero] at hphi h3
      simp only [zero_add] at h3
      linarith

end CertSound

open CertSound

/-- The contribution of the candidate `x` to the row of `s`. -/
def rcontrib (s : List (ℕ × Bool)) (x : ℕ × Bool) : ℕ :=
  if selfAvoid P.n (s ++ [x]) = true then
    match lookup keys (keyOf P.n (s ++ [x]).tail) with
    | some j => if exclWin P (s ++ [x]) = true then 0 else (if x.2 then P.wC else P.wE) * Hs[j]!
    | none => 0
  else 0

/-- A candidate that is self-avoiding and leads to an unlisted state has an excluded window. -/
def rgood (s : List (ℕ × Bool)) (x : ℕ × Bool) : Prop :=
  selfAvoid P.n (s ++ [x]) = true → lookup keys (keyOf P.n (s ++ [x]).tail) = none → exclEnding P (s ++ [x]) = true

theorem rowSum_spec {s : List (ℕ × Bool)} {tot : ℕ} (h : rowSum P keys Hs s = some tot) :
    tot = ((candList P.n).map (rcontrib P keys Hs s)).sum ∧ ∀ x ∈ candList P.n, rgood P keys s x := by
  unfold rowSum at h
  have := foldl_opt _ (rcontrib P keys Hs s) (rgood P keys s) (fun x => rfl) ?_ ?_ (candList P.n) 0 tot h
  · simpa using this
  · intro a x hx
    simp only [rgood] at hx
    simp only [rcontrib]
    by_cases h1 : selfAvoid P.n (s ++ [x]) = true
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      cases h2 : lookup keys (keyOf P.n (s ++ [x]).tail) with
      | some j =>
        simp only
        by_cases h3 : exclWin P (s ++ [x]) = true
        · simp [h3]
        · simp [h3]
      | none =>
        have h3 := hx h1 h2
        simp [h3]
    · simp only [Bool.not_eq_true] at h1
      simp [h1]
  · intro a x hx
    simp only [rgood, not_imp] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    simp only [Bool.not_eq_true] at h3
    simp [h1, h2, h3]

theorem exclWin_sound {u : List (ℕ × Bool)} (h : exclWin P u = true) : Excl P.n P.c u := by
  unfold exclWin at h
  split at h
  · exact ⟨_, h⟩
  · exact absurd h (by simp)

theorem rowCheck_spec {i : ℕ} (h : rowCheck P keys Hs i = true) :
    0 < P.Hmin ∧ P.Hmin ≤ Hs[i]! ∧ ∃ tot, rowSum P keys Hs (decodeKey P.n P.K keys[i]!) = some tot ∧
      tot * P.lamD ≤ P.lamN * P.Q * Hs[i]! := by
  unfold rowCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · rename_i tot htot
    exact ⟨tot, htot, by simpa using h3⟩
  · exact absurd h3 (by simp)

theorem isSt_lookup {s : List (ℕ × Bool)} (hs : IsSt P keys s) :
    ∃ j, lookup keys (keyOf P.n s) = some j ∧ j < keys.size ∧ keys[j]! = keyOf P.n s := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hs.2.2
  exact ⟨j, hj, lookup_some hj⟩

theorem isSt_decode (hn : 0 < P.n) {s : List (ℕ × Bool)} (hs : IsSt P keys s) :
    ∃ j, lookup keys (keyOf P.n s) = some j ∧ j < keys.size ∧ decodeKey P.n P.K keys[j]! = s := by
  obtain ⟨j, hj, hjlt, hk⟩ := isSt_lookup P keys hs
  exact ⟨j, hj, hjlt, by rw [hk, decodeKey_keyOf hn P.K s hs.1 hs.2.1]⟩

theorem hof_of_lookup {s : List (ℕ × Bool)} {j : ℕ} (hj : lookup keys (keyOf P.n s) = some j) :
    Hof P keys Hs s = Hs[j]! := by
  unfold Hof
  rw [hj]

theorem exclEnding_sound {u : List (ℕ × Bool)} (h : exclEnding P u = true) :
    ∃ m, 2 ≤ m ∧ m ≤ u.length ∧ m ≤ P.K + 1 ∧ Excl P.n P.c (u.drop (u.length - m)) := by
  unfold exclEnding at h
  rw [List.any_eq_true] at h
  obtain ⟨m, hm, hx⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [List.mem_range] at hm
  exact ⟨m, hx.1.1, hx.1.2, by omega, exclWin_sound P hx.2⟩

theorem selfAvoid_iff {n : ℕ} {u : List (ℕ × Bool)} : selfAvoid n u = true ↔ SelfAv n u := by
  unfold selfAvoid SelfAv
  exact nodupPts_iff _

theorem cert_pos (hrows : ∀ i < keys.size, rowCheck P keys Hs i = true) :
    ∀ s, IsSt P keys s → P.Hmin ≤ Hof P keys Hs s := by
  intro s hs
  obtain ⟨j, hj, hjlt, -⟩ := isSt_lookup P keys hs
  rw [hof_of_lookup P keys Hs hj]
  exact (rowCheck_spec P keys Hs (hrows j hjlt)).2.1

theorem walkPts_take_prefix (n : ℕ) : ∀ (o : List ℤ) (ds : List ℕ) (j : ℕ),
    walkPts n o (ds.take j) <+: walkPts n o ds
  | o, [], j => by simp
  | o, d :: ds, 0 => ⟨walkPts n (addP o (vecOf n d)) ds, by simp⟩
  | o, d :: ds, j + 1 => by
    simp only [List.take_succ_cons, walkPts_cons, List.cons_prefix_cons, true_and]
    exact walkPts_take_prefix n _ ds j

theorem selfAv_take {n : ℕ} {s : List (ℕ × Bool)} (h : SelfAv n s) (j : ℕ) : SelfAv n (s.take j) := by
  unfold SelfAv at h ⊢
  rw [List.map_take]
  exact h.sublist (walkPts_take_prefix n _ _ j).sublist

theorem cert_start (hn : 0 < P.n) (hdfs : dfsOK P keys P.K [] = true) :
    ∀ s, s.length = P.K → Legal P.n P.c (P.K + 1) s → IsSt P keys s := by
  intro s hlen hleg
  obtain ⟨hsa, hdir, hwin⟩ := hleg
  have key : ∀ j, j ≤ P.K → dfsOK P keys (P.K - j) (s.take j) = true := by
    intro j
    induction j with
    | zero => intro _; simpa using hdfs
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      rw [show P.K - j = (P.K - (j + 1)) + 1 by omega] at h1
      simp only [dfsOK, List.all_eq_true] at h1
      have hjs : j < s.length := by omega
      have hx := h1 s[j] (mem_candList.mpr (hdir _ (List.getElem_mem hjs)))
      rw [List.take_append_getElem hjs] at hx
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hx
      have hlt : (s.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
      rcases hx with (hx | hx) | hx
      · exfalso
        have := selfAvoid_iff.mpr (selfAv_take hsa (j + 1))
        rw [hx] at this
        exact absurd this (by simp)
      · exfalso
        obtain ⟨m, hm2, hmle, -, hex⟩ := exclEnding_sound P hx
        rw [hlt] at hmle hex
        have hw : (s.take (j + 1)).drop (j + 1 - m) = (s.drop (j + 1 - m)).take m := by
          rw [List.take_drop]
          congr 2
          omega
        rw [hw] at hex
        exact hwin (j + 1 - m) m hm2 (by omega) (by omega) hex
      · exact hx
  have hK := key P.K le_rfl
  rw [Nat.sub_self, List.take_of_length_le (by omega)] at hK
  simp only [dfsOK] at hK
  exact ⟨hlen, hdir, hK⟩

theorem cert_closed (hn : 0 < P.n) (hrows : ∀ i < keys.size, rowCheck P keys Hs i = true) :
    ∀ s, IsSt P keys s → ∀ x, Succ P.n P.c s x → IsSt P keys (s ++ [x]).tail := by
  intro s hs x hx
  obtain ⟨j, -, hjlt, hdec⟩ := isSt_decode P keys hn hs
  obtain ⟨-, -, tot, htot, -⟩ := rowCheck_spec P keys Hs (hrows j hjlt)
  rw [hdec] at htot
  obtain ⟨-, hgood⟩ := rowSum_spec P keys Hs htot
  have hg := hgood x (mem_candList.mpr hx.1)
  have hsa : selfAvoid P.n (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
  have hlen : s.length = P.K := hs.1
  refine ⟨?_, ?_, ?_⟩
  · simp [hlen]
  · intro y hy
    rcases List.mem_append.mp (List.mem_of_mem_tail hy) with hy | hy
    · exact hs.2.1 y hy
    · rw [List.mem_singleton.mp hy]
      exact hx.1
  · cases hl : lookup keys (keyOf P.n (s ++ [x]).tail) with
    | some j' => rfl
    | none =>
      exfalso
      obtain ⟨m, hm2, hmle, -, hex⟩ := exclEnding_sound P (hg hsa hl)
      have hlenu : (s ++ [x]).length = s.length + 1 := by simp
      rw [hlenu] at hmle hex
      exact hx.2.2 m hm2 hmle hex

open scoped Classical in
theorem cert_rows (hn : 0 < P.n) (hQ : 0 < P.Q) (hlamD : 0 < P.lamD)
    (hrows : ∀ i < keys.size, rowCheck P keys Hs i = true) :
    ∀ s, IsSt P keys s →
      ∑ x ∈ (cands P.n).filter (Succ P.n P.c s), wtW (ωEof P) (ωCof P) [x] * (Hof P keys Hs (s ++ [x]).tail : ℝ) ≤
        lamOf P * Hof P keys Hs s := by
  intro s hs
  obtain ⟨j, hj, hjlt, hdec⟩ := isSt_decode P keys hn hs
  obtain ⟨-, -, tot, htot, hrow⟩ := rowCheck_spec P keys Hs (hrows j hjlt)
  rw [hdec] at htot
  obtain ⟨htot_eq, -⟩ := rowSum_spec P keys Hs htot
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hQ
  have hlamDr : (0 : ℝ) < P.lamD := by exact_mod_cast hlamD
  -- each successor's term is its contribution to the computed row, divided by `Q`
  have hterm : ∀ x ∈ (cands P.n).filter (Succ P.n P.c s),
      wtW (ωEof P) (ωCof P) [x] * (Hof P keys Hs (s ++ [x]).tail : ℝ) = (rcontrib P keys Hs s x : ℝ) / P.Q := by
    intro x hxm
    have hx := (Finset.mem_filter.mp hxm).2
    have hsa : selfAvoid P.n (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
    have hnex : exclWin P (s ++ [x]) = false := by
      cases he : exclWin P (s ++ [x])
      · rfl
      · exfalso
        have hE := exclWin_sound P he
        by_cases hK : 1 ≤ s.length
        · exact hx.2.2 (s.length + 1) (by omega) le_rfl (by simpa using hE)
        · have hs0 : s = [] := List.length_eq_zero_iff.mp (by omega)
          subst hs0
          exact not_excl_single hx.1 (by simpa using hE)
    obtain ⟨j', hj', -, -⟩ := isSt_lookup P keys (cert_closed P keys Hs hn hrows s hs x hx)
    rw [hof_of_lookup P keys Hs hj']
    simp only [rcontrib, hsa, ite_true, hj', hnex, Bool.false_eq_true, ite_false]
    unfold wtW ωEof ωCof
    obtain ⟨d, b⟩ := x
    cases b <;> simp [div_mul_eq_mul_div]
  have hsumC : ∑ x ∈ cands P.n, (rcontrib P keys Hs s x : ℝ) = (tot : ℝ) := by
    rw [cands_eq_toFinset, List.sum_toFinset _ (candList_nodup _), htot_eq]
    push_cast
    rw [List.map_map]
    rfl
  calc ∑ x ∈ (cands P.n).filter (Succ P.n P.c s), wtW (ωEof P) (ωCof P) [x] * (Hof P keys Hs (s ++ [x]).tail : ℝ)
      = ∑ x ∈ (cands P.n).filter (Succ P.n P.c s), (rcontrib P keys Hs s x : ℝ) / P.Q := Finset.sum_congr rfl hterm
    _ ≤ ∑ x ∈ cands P.n, (rcontrib P keys Hs s x : ℝ) / P.Q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (tot : ℝ) / P.Q := by rw [← Finset.sum_div, hsumC]
    _ ≤ lamOf P * Hof P keys Hs s := by
        rw [hof_of_lookup P keys Hs hj, lamOf, div_le_iff₀ hQr]
        have hrow' : (tot : ℝ) * P.lamD ≤ P.lamN * P.Q * (Hs[j]! : ℝ) := by exact_mod_cast hrow
        rw [show (P.lamN : ℝ) / P.lamD * (Hs[j]! : ℝ) * P.Q = (P.lamN * P.Q * (Hs[j]! : ℝ)) / P.lamD by ring,
          le_div_iff₀ hlamDr]
        exact hrow'

/-! ## The start sum -/

theorem foldl_add_sum (f : ℕ → ℕ) : ∀ (L : List ℕ) (a : ℕ),
    L.foldl (fun acc c => acc + f c) a = a + (L.map f).sum
  | [], a => by simp
  | x :: L, a => by
    simp only [List.foldl, List.map_cons, List.sum_cons]
    rw [foldl_add_sum f L]
    omega

theorem nCOf_le (n K k : ℕ) : nCOf n K k ≤ K := by
  unfold nCOf
  calc ((decodeKey n K k).filter (fun x => x.2)).length ≤ (decodeKey n K k).length := List.length_filter_le _ _
    _ = K := length_decodeKey n K k

/-- A fold that adds `h i` at the slot `g i`. -/
theorem foldl_setAdd (g h : ℕ → ℕ) (F : Array ℕ → ℕ → Array ℕ)
    (hF : ∀ acc i, F acc i = acc.set! (g i) (acc[g i]! + h i)) (K : ℕ) (hg : ∀ i, g i ≤ K) :
    ∀ (L : List ℕ) (acc : Array ℕ), acc.size = K + 1 →
      (L.foldl F acc).size = K + 1 ∧
        ∀ c ≤ K, (L.foldl F acc)[c]! = acc[c]! + ((L.filter (fun i => g i = c)).map h).sum
  | [], acc, hs => by simp [hs]
  | i :: L, acc, hs => by
    simp only [List.foldl]
    have hs' : (F acc i).size = K + 1 := by rw [hF, Array.size_set!, hs]
    obtain ⟨h1, h2⟩ := foldl_setAdd g h F hF K hg L (F acc i) hs'
    refine ⟨h1, fun c hc => ?_⟩
    rw [h2 c hc, hF]
    by_cases hgc : g i = c
    · subst hgc
      rw [Array.getElem!_set!_self _ _ _ (by have := hg i; omega)]
      simp only [List.filter_cons, decide_true, ite_true, List.map_cons, List.sum_cons]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hgc]
      simp [hgc]

/-- The sums of `H` by number of C-labels. -/
theorem totByC_spec {c : ℕ} (hc : c ≤ P.K) :
    (totByC P keys Hs)[c]! =
      (((List.range keys.size).filter (fun i => nCOf P.n P.K keys[i]! = c)).map (fun i => Hs[i]!)).sum := by
  have key := foldl_setAdd (fun i => nCOf P.n P.K keys[i]!) (fun i => Hs[i]!)
    (fun acc i => let c := nCOf P.n P.K keys[i]!; acc.set! c (acc[c]! + Hs[i]!)) (fun _ _ => rfl) P.K
    (fun i => nCOf_le _ _ _) (List.range keys.size) (Array.replicate (P.K + 1) 0) (by simp)
  unfold totByC
  rw [key.2 c hc]
  have h0 : (Array.replicate (P.K + 1) (0 : ℕ))[c]! = 0 := by
    rw [getElem!_pos _ _ (by simp; omega)]
    simp
  rw [h0, Nat.zero_add]

theorem toFinset_range' (a : ℕ) : (List.range a).toFinset = Finset.range a := by
  ext x
  simp

theorem list_sum_range (m : ℕ) (f : ℕ → ℕ) : ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  rw [← toFinset_range', List.sum_toFinset _ List.nodup_range]

theorem list_filter_sum_range (m : ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ) :
    (((List.range m).filter (fun i => decide (p i))).map f).sum = ∑ i ∈ (Finset.range m).filter p, f i := by
  rw [← List.sum_toFinset _ (List.nodup_range.filter _)]
  congr 1
  ext x
  simp

/-- The weight of a pattern in closed form. -/
theorem wtW_eq (a b : ℝ) : ∀ s : List (ℕ × Bool),
    wtW a b s = a ^ (s.length - (s.filter (fun x => x.2)).length) * b ^ (s.filter (fun x => x.2)).length
  | [] => by simp [wtW]
  | x :: s => by
    have ih := wtW_eq a b s
    have hle : (s.filter (fun x => x.2)).length ≤ s.length := List.length_filter_le _ _
    unfold wtW at ih ⊢
    obtain ⟨d, l⟩ := x
    cases l
    · simp only [List.map_cons, List.prod_cons, Bool.false_eq_true, ite_false, List.filter_cons,
        List.length_cons]
      rw [ih, show s.length + 1 - (List.filter (fun x => x.2) s).length =
        (s.length - (List.filter (fun x => x.2) s).length) + 1 by omega, pow_succ]
      ring
    · simp only [List.map_cons, List.prod_cons, ite_true, List.filter_cons, List.length_cons]
      rw [ih, show s.length + 1 - ((List.filter (fun x => x.2) s).length + 1) =
        s.length - (List.filter (fun x => x.2) s).length by omega, pow_succ]
      ring

open scoped Classical in
theorem cert_startSum (hn : 0 < P.n) (hQ : 0 < P.Q) (hK0d : 0 < P.K0d) (hHmin : 0 < P.Hmin)
    (hrows : ∀ i < keys.size, rowCheck P keys Hs i = true) (hst : startOK P keys Hs = true) :
    (ωEof P + ωCof P) ^ 2 *
        ((∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (ωEof P) (ωCof P) s * (Hof P keys Hs s : ℝ)) / P.Hmin) ≤
      (P.K0n : ℝ) / P.K0d := by
  -- the term of index `i`: `H_i ω_E^(K - c_i) ω_C^(c_i)`, scaled by `Q^K`
  let Tt : ℕ → ℕ := fun i => Hs[i]! * P.wE ^ (P.K - nCOf P.n P.K keys[i]!) * P.wC ^ (nCOf P.n P.K keys[i]!)
  -- (1) the computed `S` is `∑ i, Tt i`
  have hS : (List.range (P.K + 1)).foldl
      (fun acc c => acc + (totByC P keys Hs)[c]! * P.wE ^ (P.K - c) * P.wC ^ c) 0 =
        ∑ i ∈ Finset.range keys.size, Tt i := by
    rw [foldl_add_sum, Nat.zero_add, list_sum_range]
    have hc : ∀ c ∈ Finset.range (P.K + 1), (totByC P keys Hs)[c]! * P.wE ^ (P.K - c) * P.wC ^ c =
        ∑ i ∈ (Finset.range keys.size).filter (fun i => nCOf P.n P.K keys[i]! = c), Tt i := by
      intro c hcm
      rw [Finset.mem_range] at hcm
      rw [totByC_spec P keys Hs (by omega), list_filter_sum_range keys.size (fun i => nCOf P.n P.K keys[i]! = c),
        Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_filter] at hi
      simp only [Tt, hi.2]
    rw [Finset.sum_congr rfl hc]
    exact Finset.sum_fiberwise_of_maps_to
      (fun i _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (nCOf_le _ _ _))) Tt
  -- (2) the start check
  have hst' : (P.wE + P.wC) ^ 2 * (∑ i ∈ Finset.range keys.size, Tt i) * P.K0d ≤
      P.K0n * P.Hmin * P.Q ^ (P.K + 2) := by
    unfold startOK at hst
    simp only [decide_eq_true_eq] at hst
    rw [← hS]
    exact hst
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hQ
  have hHr : (0 : ℝ) < P.Hmin := by exact_mod_cast hHmin
  have hKr : (0 : ℝ) < P.K0d := by exact_mod_cast hK0d
  -- (3) the sum over the listed states is at most `∑ i, Tt i / Q^K`
  have hreal : ∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (ωEof P) (ωCof P) s * (Hof P keys Hs s : ℝ) ≤
      ∑ i ∈ Finset.range keys.size, (Tt i : ℝ) / (P.Q : ℝ) ^ P.K := by
    apply Finset.sum_le_sum_of_injOn (fun s => (lookup keys (keyOf P.n s)).getD 0)
    · intro s hs t ht hst
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs ht
      obtain ⟨j, hj, -, hk⟩ := isSt_lookup P keys hs.2
      obtain ⟨j', hj', -, hk'⟩ := isSt_lookup P keys ht.2
      simp only [hj, hj', Option.getD_some] at hst
      subst hst
      exact keyOf_inj hn hs.2.1 ht.2.1 hs.2.2.1 ht.2.2.1 (hk.symm.trans hk')
    · intro j hj
      simp only [Finset.mem_image, Finset.mem_filter] at hj
      obtain ⟨s, ⟨-, hs⟩, rfl⟩ := hj
      obtain ⟨j, hj, hjlt, -⟩ := isSt_lookup P keys hs
      simp only [hj, Option.getD_some, Finset.mem_range]
      exact hjlt
    · intro s hs
      rw [Finset.mem_filter] at hs
      obtain ⟨j, hj, -, hdec⟩ := isSt_decode P keys hn hs.2
      simp only [hj, Option.getD_some]
      rw [hof_of_lookup P keys Hs hj]
      have hG : nCOf P.n P.K keys[j]! = (s.filter (fun x => x.2)).length := by
        simp only [nCOf, hdec]
      have hGK : nCOf P.n P.K keys[j]! ≤ P.K := nCOf_le _ _ _
      have hlen : s.length = P.K := hs.2.1
      rw [wtW_eq, hlen, ← hG]
      apply le_of_eq
      simp only [Tt, ωEof, ωCof]
      push_cast
      rw [div_pow, div_pow]
      have hQK : (P.Q : ℝ) ^ P.K = (P.Q : ℝ) ^ (P.K - nCOf P.n P.K keys[j]!) * (P.Q : ℝ) ^ nCOf P.n P.K keys[j]! := by
        rw [← pow_add, Nat.sub_add_cancel hGK]
      rw [hQK]
      field_simp
    · intro j _ _
      positivity
  -- (4) the final inequality
  have hsum_eq : ∑ i ∈ Finset.range keys.size, (Tt i : ℝ) / (P.Q : ℝ) ^ P.K =
      ((∑ i ∈ Finset.range keys.size, Tt i : ℕ) : ℝ) / (P.Q : ℝ) ^ P.K := by
    rw [← Finset.sum_div]
    push_cast
    rfl
  rw [hsum_eq] at hreal
  have hst_r : ((P.wE : ℝ) + P.wC) ^ 2 * ((∑ i ∈ Finset.range keys.size, Tt i : ℕ) : ℝ) * P.K0d ≤
      P.K0n * P.Hmin * (P.Q : ℝ) ^ (P.K + 2) := by exact_mod_cast hst'
  calc (ωEof P + ωCof P) ^ 2 *
        ((∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (ωEof P) (ωCof P) s * (Hof P keys Hs s : ℝ)) / P.Hmin)
      ≤ (ωEof P + ωCof P) ^ 2 *
          ((((∑ i ∈ Finset.range keys.size, Tt i : ℕ) : ℝ) / (P.Q : ℝ) ^ P.K) / P.Hmin) := by
        gcongr
    _ = (((P.wE : ℝ) + P.wC) ^ 2 * ((∑ i ∈ Finset.range keys.size, Tt i : ℕ) : ℝ)) /
          ((P.Q : ℝ) ^ (P.K + 2) * P.Hmin) := by
        unfold ωEof ωCof
        field_simp
        ring
    _ ≤ (P.K0n : ℝ) / P.K0d := by
        rw [div_le_div_iff₀ (by positivity) hKr]
        nlinarith [hst_r]

end QEC
