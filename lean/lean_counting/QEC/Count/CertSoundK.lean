import QEC.Count.CertSound
import QECCountComp.Kern

/-!
# Soundness of the kernel-friendly certificate checks (`QECCountComp/Kern.lean`)

The listed states are the entries of a tree `t : KTree`; `IsStK`, `HofK` are as `IsSt`, `Hof` with `t.find` in place
of `lookup`. From the checks (`rowCheckK` for every entry of `t.toList`, `dfsOKK`, `startOKK`) we get the same
hypotheses of `sum_legal_le` as in `CertSound.lean`. The tree need not be a search tree for soundness: `find` only
returns entries of the tree (`find_mem`). Also the chunk lemmas for the kernel checks.
-/

namespace QEC

open Finset QECComp

variable (P : Params) (t : KTree)

/-- The listed states of a tree. -/
def IsStK (s : List (ℕ × Bool)) : Prop :=
  s.length = P.K ∧ DirOK P.n s ∧ (t.find (keyOf P.n s)).isSome = true

/-- The potential of a tree: `H` of a listed state, `0` off the list. -/
def HofK (s : List (ℕ × Bool)) : ℕ :=
  match t.find (keyOf P.n s) with
  | some hm => hm.1
  | none => 0

theorem find_mem {t : KTree} {x h m : ℕ} (hf : t.find x = some (h, m)) : (x, h, m) ∈ t.toList := by
  induction t with
  | leaf => simp [KTree.find] at hf
  | node l k h0 m0 r ihl ihr =>
    simp only [KTree.find] at hf
    simp only [KTree.toList, List.mem_append, List.mem_cons]
    by_cases h1 : Nat.blt x k = true
    · rw [if_pos h1] at hf
      exact Or.inl (ihl hf)
    · rw [if_neg h1] at hf
      by_cases h2 : Nat.blt k x = true
      · rw [if_pos h2] at hf
        exact Or.inr (Or.inr (ihr hf))
      · rw [if_neg h2] at hf
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        rw [Nat.blt_eq] at h1 h2
        have hxk : x = k := by omega
        subst hxk
        exact Or.inr (Or.inl rfl)

theorem exclWinK_sound {u : List (ℕ × Bool)} (h : exclWinK P u = true) : Excl P.n P.c u := by
  unfold exclWinK at h
  split at h
  · exact ⟨_, h⟩
  · exact absurd h (by simp)

namespace CertSoundK

theorem length_candList (n : ℕ) : (candList n).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : List.range (2 * (n + 1)) = List.range (2 * n) ++ [2 * n, 2 * n + 1] := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ, List.append_assoc]
      rfl
    unfold candList at ih ⊢
    rw [h, List.flatMap_append, List.length_append, ih]
    simp
    ring

theorem zip_nodup (n : ℕ) : ((candList n).zip (List.range (4 * n))).Nodup := by
  apply List.Nodup.of_map Prod.fst
  rw [List.map_fst_zip (by simp [length_candList])]
  exact CertSound.candList_nodup n

theorem mem_zip_idx {n : ℕ} {x : ℕ × Bool} (hx : x ∈ candList n) :
    (x, (candList n).idxOf x) ∈ (candList n).zip (List.range (4 * n)) := by
  have hlen := length_candList n
  have hi : (candList n).idxOf x < (candList n).length := List.idxOf_lt_length_of_mem hx
  have hget : (candList n)[(candList n).idxOf x] = x := List.getElem_idxOf hi
  rw [List.mem_iff_getElem]
  refine ⟨(candList n).idxOf x, by simp only [List.length_zip, List.length_range]; omega, ?_⟩
  simp only [List.getElem_zip, List.getElem_range, hget]

end CertSoundK

open CertSound CertSoundK

/-- The contribution of the candidate `xi` (step, index) to the row of `s` with mask `mask`. -/
def rcontribK (mask : ℕ) (s : List (ℕ × Bool)) (xi : (ℕ × Bool) × ℕ) : ℕ :=
  if selfAvoid P.n (s ++ [xi.1]) = true then
    match t.find (keyOf P.n (s ++ [xi.1]).tail) with
    | some hm => if (mask / 2 ^ xi.2 % 2 == 1) = true then 0 else (if xi.1.2 then P.wC else P.wE) * hm.1
    | none => 0
  else 0

/-- A candidate with a claimed exclusion has a checked exclusion; a self-avoiding candidate with an unlisted
target has an excluded window. -/
def rgoodK (mask : ℕ) (s : List (ℕ × Bool)) (xi : (ℕ × Bool) × ℕ) : Prop :=
  selfAvoid P.n (s ++ [xi.1]) = true →
    match t.find (keyOf P.n (s ++ [xi.1]).tail) with
    | some _ => (mask / 2 ^ xi.2 % 2 == 1) = true → exclWinK P (s ++ [xi.1]) = true
    | none => exclEndingK P (s ++ [xi.1]) = true

theorem rowSumK_spec {mask : ℕ} {s : List (ℕ × Bool)} {tot : ℕ} (h : rowSumK P t mask s = some tot) :
    tot = (((candList P.n).zip (List.range (4 * P.n))).map (rcontribK P t mask s)).sum ∧
      ∀ xi ∈ (candList P.n).zip (List.range (4 * P.n)), rgoodK P t mask s xi := by
  unfold rowSumK at h
  have := foldl_opt _ (rcontribK P t mask s) (rgoodK P t mask s) (fun x => rfl) ?_ ?_ _ 0 tot h
  · simpa using this
  · intro a xi hx
    simp only [rgoodK] at hx
    simp only [rcontribK]
    by_cases h1 : selfAvoid P.n (s ++ [xi.1]) = true
    · have hx1 := hx h1
      simp only [h1, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      cases h2 : t.find (keyOf P.n (s ++ [xi.1]).tail) with
      | some hm =>
        rw [h2] at hx1
        simp only
        by_cases h3 : (mask / 2 ^ xi.2 % 2 == 1) = true
        · have h4 := hx1 h3
          simp [h3, h4]
        · simp [h3]
      | none =>
        rw [h2] at hx1
        simp [hx1]
    · simp only [Bool.not_eq_true] at h1
      simp [h1]
  · intro a xi hx
    simp only [rgoodK] at hx
    by_cases h1 : selfAvoid P.n (s ++ [xi.1]) = true
    · have hx' : ¬ (match t.find (keyOf P.n (s ++ [xi.1]).tail) with
          | some _ => (mask / 2 ^ xi.2 % 2 == 1) = true → exclWinK P (s ++ [xi.1]) = true
          | none => exclEndingK P (s ++ [xi.1]) = true) := fun h' => hx (fun _ => h')
      simp only [h1, Bool.not_true, Bool.false_eq_true, ite_false]
      cases h2 : t.find (keyOf P.n (s ++ [xi.1]).tail) with
      | some hm =>
        rw [h2] at hx'
        simp only [not_imp, Bool.not_eq_true] at hx'
        simp [hx'.1, hx'.2]
      | none =>
        rw [h2] at hx'
        simp only [Bool.not_eq_true] at hx'
        simp [hx']
    · exact absurd (fun h => absurd h h1) hx

theorem rowCheckK_spec {e : ℕ × ℕ × ℕ} (h : rowCheckK P t e = true) :
    0 < P.Hmin ∧ P.Hmin ≤ e.2.1 ∧ ∃ tot, rowSumK P t e.2.2 (decodeKey P.n P.K e.1) = some tot ∧
      tot * P.lamD ≤ P.lamN * P.Q * e.2.1 := by
  unfold rowCheckK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · rename_i tot htot
    exact ⟨tot, htot, by simpa using h3⟩
  · exact absurd h3 (by simp)

theorem isStK_find {s : List (ℕ × Bool)} (hs : IsStK P t s) :
    ∃ h m, t.find (keyOf P.n s) = some (h, m) ∧ (keyOf P.n s, h, m) ∈ t.toList := by
  obtain ⟨⟨h, m⟩, hf⟩ := Option.isSome_iff_exists.mp hs.2.2
  exact ⟨h, m, hf, find_mem hf⟩

theorem hofK_of_find {s : List (ℕ × Bool)} {h m : ℕ} (hf : t.find (keyOf P.n s) = some (h, m)) :
    HofK P t s = h := by
  unfold HofK
  rw [hf]

theorem exclEndingK_sound {u : List (ℕ × Bool)} (h : exclEndingK P u = true) :
    ∃ m, 2 ≤ m ∧ m ≤ u.length ∧ m ≤ P.K + 1 ∧ Excl P.n P.c (u.drop (u.length - m)) := by
  unfold exclEndingK at h
  rw [List.any_eq_true] at h
  obtain ⟨m, hm, hx⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [List.mem_range] at hm
  exact ⟨m, hx.1.1, hx.1.2, by omega, exclWinK_sound P hx.2⟩

theorem certK_pos (hrows : ∀ e ∈ t.toList, rowCheckK P t e = true) :
    ∀ s, IsStK P t s → P.Hmin ≤ HofK P t s := by
  intro s hs
  obtain ⟨h, m, hf, hmem⟩ := isStK_find P t hs
  rw [hofK_of_find P t hf]
  exact (rowCheckK_spec P t (hrows _ hmem)).2.1

theorem certK_start (hn : 0 < P.n) (hdfs : dfsOKK P t P.K [] = true) :
    ∀ s, s.length = P.K → Legal P.n P.c (P.K + 1) s → IsStK P t s := by
  intro s hlen hleg
  obtain ⟨hsa, hdir, hwin⟩ := hleg
  have key : ∀ j, j ≤ P.K → dfsOKK P t (P.K - j) (s.take j) = true := by
    intro j
    induction j with
    | zero => intro _; simpa using hdfs
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      rw [show P.K - j = (P.K - (j + 1)) + 1 by omega] at h1
      simp only [dfsOKK, List.all_eq_true] at h1
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
        obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingK_sound P hx
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
  simp only [dfsOKK] at hK
  exact ⟨hlen, hdir, hK⟩

theorem certK_closed (hn : 0 < P.n) (hrows : ∀ e ∈ t.toList, rowCheckK P t e = true) :
    ∀ s, IsStK P t s → ∀ x, Succ P.n P.c s x → IsStK P t (s ++ [x]).tail := by
  intro s hs x hx
  obtain ⟨h0, m0, hf, hmem⟩ := isStK_find P t hs
  obtain ⟨-, -, tot, htot, -⟩ := rowCheckK_spec P t (hrows _ hmem)
  simp only at htot
  rw [decodeKey_keyOf hn P.K s hs.1 hs.2.1] at htot
  obtain ⟨-, hgood⟩ := rowSumK_spec P t htot
  have hg := hgood _ (mem_zip_idx (mem_candList.mpr hx.1))
  have hsa : selfAvoid P.n (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
  have hlen : s.length = P.K := hs.1
  refine ⟨?_, ?_, ?_⟩
  · simp [hlen]
  · intro y hy
    rcases List.mem_append.mp (List.mem_of_mem_tail hy) with hy | hy
    · exact hs.2.1 y hy
    · rw [List.mem_singleton.mp hy]
      exact hx.1
  · cases hl : t.find (keyOf P.n (s ++ [x]).tail) with
    | some hm => rfl
    | none =>
      exfalso
      have hg' := hg hsa
      simp only at hg'
      rw [hl] at hg'
      obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingK_sound P hg'
      have hlenu : (s ++ [x]).length = s.length + 1 := by simp
      rw [hlenu] at hmle hex
      exact hx.2.2 m hm2 hmle hex

open scoped Classical in
theorem certK_rows (hn : 0 < P.n) (hQ : 0 < P.Q) (hlamD : 0 < P.lamD)
    (hrows : ∀ e ∈ t.toList, rowCheckK P t e = true) :
    ∀ s, IsStK P t s →
      ∑ x ∈ (cands P.n).filter (Succ P.n P.c s), wtW (ωEof P) (ωCof P) [x] * (HofK P t (s ++ [x]).tail : ℝ) ≤
        lamOf P * HofK P t s := by
  intro s hs
  obtain ⟨h0, m0, hf, hmem⟩ := isStK_find P t hs
  obtain ⟨-, -, tot, htot, hrow⟩ := rowCheckK_spec P t (hrows _ hmem)
  simp only at htot hrow
  rw [decodeKey_keyOf hn P.K s hs.1 hs.2.1] at htot
  obtain ⟨htot_eq, hgood⟩ := rowSumK_spec P t htot
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hQ
  have hlamDr : (0 : ℝ) < P.lamD := by exact_mod_cast hlamD
  set Z := (candList P.n).zip (List.range (4 * P.n)) with hZ
  let f : ℕ × Bool → (ℕ × Bool) × ℕ := fun x => (x, (candList P.n).idxOf x)
  -- each successor's term is the contribution of its candidate to the computed row, divided by `Q`
  have hterm : ∀ x ∈ (cands P.n).filter (Succ P.n P.c s),
      wtW (ωEof P) (ωCof P) [x] * (HofK P t (s ++ [x]).tail : ℝ) = (rcontribK P t m0 s (f x) : ℝ) / P.Q := by
    intro x hxm
    have hx := (Finset.mem_filter.mp hxm).2
    have hsa : selfAvoid P.n (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
    obtain ⟨h1, m1, hf1, -⟩ := isStK_find P t (certK_closed P t hn hrows s hs x hx)
    have hg := hgood (f x) (mem_zip_idx (mem_candList.mpr hx.1)) hsa
    simp only [f] at hg
    rw [hf1] at hg
    have hbit : (m0 / 2 ^ (candList P.n).idxOf x % 2 == 1) = false := by
      cases hb : (m0 / 2 ^ (candList P.n).idxOf x % 2 == 1)
      · rfl
      · exfalso
        have hE := exclWinK_sound P (hg hb)
        by_cases hK : 1 ≤ s.length
        · exact hx.2.2 (s.length + 1) (by omega) le_rfl (by simpa using hE)
        · have hs0 : s = [] := List.length_eq_zero_iff.mp (by omega)
          subst hs0
          exact not_excl_single hx.1 (by simpa using hE)
    rw [hofK_of_find P t hf1]
    simp only [rcontribK, f, hsa, ite_true, hf1, hbit, Bool.false_eq_true, ite_false]
    unfold wtW ωEof ωCof
    obtain ⟨d, b⟩ := x
    cases b <;> simp [div_mul_eq_mul_div]
  have hinj : Set.InjOn f ↑((cands P.n).filter (Succ P.n P.c s)) := by
    intro x _ y _ hxy
    exact (Prod.mk.inj hxy).1
  have himg : ((cands P.n).filter (Succ P.n P.c s)).image f ⊆ Z.toFinset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [List.mem_toFinset]
    exact mem_zip_idx (mem_candList.mpr (Finset.mem_filter.mp hx).2.1)
  have hsumZ : ∑ y ∈ Z.toFinset, (rcontribK P t m0 s y : ℝ) = (tot : ℝ) := by
    rw [List.sum_toFinset _ (zip_nodup P.n), htot_eq]
    push_cast
    rw [List.map_map]
    rfl
  calc ∑ x ∈ (cands P.n).filter (Succ P.n P.c s), wtW (ωEof P) (ωCof P) [x] * (HofK P t (s ++ [x]).tail : ℝ)
      = ∑ x ∈ (cands P.n).filter (Succ P.n P.c s), (rcontribK P t m0 s (f x) : ℝ) / P.Q :=
        Finset.sum_congr rfl hterm
    _ = ∑ y ∈ ((cands P.n).filter (Succ P.n P.c s)).image f, (rcontribK P t m0 s y : ℝ) / P.Q :=
        (Finset.sum_image (f := fun y => (rcontribK P t m0 s y : ℝ) / P.Q) hinj).symm
    _ ≤ ∑ y ∈ Z.toFinset, (rcontribK P t m0 s y : ℝ) / P.Q :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
    _ = (tot : ℝ) / P.Q := by rw [← Finset.sum_div, hsumZ]
    _ ≤ lamOf P * HofK P t s := by
        rw [hofK_of_find P t hf, lamOf, div_le_iff₀ hQr]
        have hrow' : (tot : ℝ) * P.lamD ≤ P.lamN * P.Q * (h0 : ℝ) := by exact_mod_cast hrow
        rw [show (P.lamN : ℝ) / P.lamD * (h0 : ℝ) * P.Q = (P.lamN * P.Q * (h0 : ℝ)) / P.lamD by ring,
          le_div_iff₀ hlamDr]
        exact hrow'

/-! ## The start sum -/

namespace CertSoundK

/-- A fold that adds `h e` at the slot `g e` of a list. -/
theorem foldl_setAddL {α : Type*} (g h : α → ℕ) (K : ℕ) (hg : ∀ e, g e ≤ K) :
    ∀ (L : List α) (acc : List ℕ), acc.length = K + 1 →
      (L.foldl (fun (acc : List ℕ) e => acc.set (g e) (acc.getD (g e) 0 + h e)) acc).length = K + 1 ∧
        ∀ c ≤ K, (L.foldl (fun (acc : List ℕ) e => acc.set (g e) (acc.getD (g e) 0 + h e)) acc).getD c 0 =
          acc.getD c 0 + ((L.filter (fun e => g e = c)).map h).sum
  | [], acc, hs => by simp [hs]
  | e :: L, acc, hs => by
    simp only [List.foldl]
    have hs' : (acc.set (g e) (acc.getD (g e) 0 + h e)).length = K + 1 := by rw [List.length_set, hs]
    obtain ⟨h1, h2⟩ := foldl_setAddL g h K hg L _ hs'
    refine ⟨h1, fun c hc => ?_⟩
    rw [h2 c hc]
    have hge := hg e
    by_cases hgc : g e = c
    · subst hgc
      have hset : (acc.set (g e) (acc.getD (g e) 0 + h e)).getD (g e) 0 = acc.getD (g e) 0 + h e := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl, if_pos (by omega)]
        rfl
      rw [hset]
      simp only [List.filter_cons, decide_true, ite_true, List.map_cons, List.sum_cons]
      omega
    · have hset : (acc.set (g e) (acc.getD (g e) 0 + h e)).getD c 0 = acc.getD c 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_neg hgc, ← List.getD_eq_getElem?_getD]
      rw [hset]
      simp [hgc]

end CertSoundK

open scoped Classical in
theorem certK_startSum (hn : 0 < P.n) (hQ : 0 < P.Q) (hK0d : 0 < P.K0d) (hHmin : 0 < P.Hmin)
    (hrows : ∀ e ∈ t.toList, rowCheckK P t e = true) (hst : startOKK P t = true) :
    (ωEof P + ωCof P) ^ 2 *
        ((∑ s ∈ (pats P.n P.K).filter (IsStK P t), wtW (ωEof P) (ωCof P) s * (HofK P t s : ℝ)) / P.Hmin) ≤
      (P.K0n : ℝ) / P.K0d := by
  set L := t.toList with hL
  -- the term of an entry: `H ω_E^(K - c) ω_C^c`, scaled by `Q^K`
  let Tt : ℕ × ℕ × ℕ → ℕ := fun e => e.2.1 * P.wE ^ (P.K - nCOf P.n P.K e.1) * P.wC ^ (nCOf P.n P.K e.1)
  -- (1) the computed `S` is `∑ e ∈ L, Tt e`
  have hspec := foldl_setAddL (fun e : ℕ × ℕ × ℕ => nCOf P.n P.K e.1) (fun e => e.2.1) P.K
    (fun e => nCOf_le _ _ _) L (List.replicate (P.K + 1) 0) (by simp)
  set tot := L.foldl (fun (acc : List ℕ) e =>
    acc.set (nCOf P.n P.K e.1) (acc.getD (nCOf P.n P.K e.1) 0 + e.2.1)) (List.replicate (P.K + 1) 0) with htot
  have hS : (List.range (P.K + 1)).foldl (fun acc c => acc + tot.getD c 0 * P.wE ^ (P.K - c) * P.wC ^ c) 0 =
      (L.map Tt).sum := by
    rw [foldl_add_sum, Nat.zero_add, list_sum_range]
    have hc : ∀ c ∈ Finset.range (P.K + 1), tot.getD c 0 * P.wE ^ (P.K - c) * P.wC ^ c =
        ((L.filter (fun e => nCOf P.n P.K e.1 = c)).map Tt).sum := by
      intro c hcm
      rw [Finset.mem_range] at hcm
      rw [hspec.2 c (by omega)]
      have h0 : (List.replicate (P.K + 1) (0 : ℕ)).getD c 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split <;> rfl
      rw [h0, Nat.zero_add, ← List.sum_map_mul_right, ← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro e he
      have := (List.mem_filter.mp he).2
      simp only [decide_eq_true_eq] at this
      simp only [Function.comp, Tt, this]
    rw [Finset.sum_congr rfl hc]
    -- regroup the list sum by the number of C-labels
    have hfib : ∀ (M : List (ℕ × ℕ × ℕ)), (∀ e ∈ M, nCOf P.n P.K e.1 ≤ P.K) →
        ∑ c ∈ Finset.range (P.K + 1), ((M.filter (fun e => nCOf P.n P.K e.1 = c)).map Tt).sum = (M.map Tt).sum := by
      intro M
      induction M with
      | nil => intro _; simp
      | cons e M ih =>
        intro hM
        have hle := hM e List.mem_cons_self
        rw [List.map_cons, List.sum_cons, ← ih (fun e' he' => hM e' (List.mem_cons_of_mem _ he'))]
        have hsplit : ∀ c, ((List.filter (fun e' => nCOf P.n P.K e'.1 = c) (e :: M)).map Tt).sum =
            (if nCOf P.n P.K e.1 = c then Tt e else 0) + ((M.filter (fun e' => nCOf P.n P.K e'.1 = c)).map Tt).sum := by
          intro c
          by_cases hc : nCOf P.n P.K e.1 = c
          · simp [List.filter_cons, hc]
          · simp [List.filter_cons, hc]
        rw [Finset.sum_congr rfl (fun c _ => hsplit c), Finset.sum_add_distrib, Finset.sum_ite_eq]
        simp only [Finset.mem_range, show nCOf P.n P.K e.1 < P.K + 1 by omega, ite_true]
    exact hfib L (fun e _ => nCOf_le _ _ _)
  -- (2) the start check
  have hst' : (P.wE + P.wC) ^ 2 * (L.map Tt).sum * P.K0d ≤ P.K0n * P.Hmin * P.Q ^ (P.K + 2) := by
    unfold startOKK at hst
    simp only [decide_eq_true_eq] at hst
    rw [← hS]
    exact hst
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hQ
  have hHr : (0 : ℝ) < P.Hmin := by exact_mod_cast hHmin
  have hKr : (0 : ℝ) < P.K0d := by exact_mod_cast hK0d
  -- (3) the sum over the listed states is at most `∑ e ∈ L, Tt e / Q^K`
  let φ : List (ℕ × Bool) → ℕ × ℕ × ℕ := fun s =>
    match t.find (keyOf P.n s) with
    | some hm => (keyOf P.n s, hm.1, hm.2)
    | none => (0, 0, 0)
  have hφ : ∀ s, IsStK P t s → ∃ h m, t.find (keyOf P.n s) = some (h, m) ∧ φ s = (keyOf P.n s, h, m) := by
    intro s hs
    obtain ⟨h, m, hf, -⟩ := isStK_find P t hs
    exact ⟨h, m, hf, by simp only [φ, hf]⟩
  have hreal : ∑ s ∈ (pats P.n P.K).filter (IsStK P t), wtW (ωEof P) (ωCof P) s * (HofK P t s : ℝ) ≤
      ((L.map Tt).sum : ℝ) / (P.Q : ℝ) ^ P.K := by
    have hinj : Set.InjOn φ ↑((pats P.n P.K).filter (IsStK P t)) := by
      intro s hs s' hs' hss
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hs hs'
      obtain ⟨h, m, hf, he⟩ := hφ s hs.2
      obtain ⟨h', m', hf', he'⟩ := hφ s' hs'.2
      rw [he, he'] at hss
      have hk := (Prod.mk.inj hss).1
      exact keyOf_inj hn hs.2.1 hs'.2.1 hs.2.2.1 hs'.2.2.1 hk
    have hterm : ∀ s ∈ (pats P.n P.K).filter (IsStK P t),
        wtW (ωEof P) (ωCof P) s * (HofK P t s : ℝ) = (Tt (φ s) : ℝ) / (P.Q : ℝ) ^ P.K := by
      intro s hs
      rw [Finset.mem_filter] at hs
      obtain ⟨h, m, hf, he⟩ := hφ s hs.2
      rw [he, hofK_of_find P t hf]
      have hG : nCOf P.n P.K (keyOf P.n s) = (s.filter (fun x => x.2)).length := by
        simp only [nCOf, decodeKey_keyOf hn P.K s hs.2.1 hs.2.2.1]
      have hGK : nCOf P.n P.K (keyOf P.n s) ≤ P.K := nCOf_le _ _ _
      have hlen : s.length = P.K := hs.2.1
      rw [wtW_eq, hlen, ← hG]
      simp only [Tt, ωEof, ωCof]
      push_cast
      rw [div_pow, div_pow]
      have hQK : (P.Q : ℝ) ^ P.K = (P.Q : ℝ) ^ (P.K - nCOf P.n P.K (keyOf P.n s)) *
          (P.Q : ℝ) ^ nCOf P.n P.K (keyOf P.n s) := by
        rw [← pow_add, Nat.sub_add_cancel hGK]
      rw [hQK]
      field_simp
    have himg : ((pats P.n P.K).filter (IsStK P t)).image φ ⊆ L.toFinset := by
      intro e he
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨h, m, hf, he'⟩ := hφ s (Finset.mem_filter.mp hs).2
      rw [he', List.mem_toFinset]
      exact find_mem hf
    calc ∑ s ∈ (pats P.n P.K).filter (IsStK P t), wtW (ωEof P) (ωCof P) s * (HofK P t s : ℝ)
        = ∑ s ∈ (pats P.n P.K).filter (IsStK P t), (Tt (φ s) : ℝ) / (P.Q : ℝ) ^ P.K :=
          Finset.sum_congr rfl hterm
      _ = ∑ e ∈ ((pats P.n P.K).filter (IsStK P t)).image φ, (Tt e : ℝ) / (P.Q : ℝ) ^ P.K :=
          (Finset.sum_image (f := fun e => (Tt e : ℝ) / (P.Q : ℝ) ^ P.K) hinj).symm
      _ ≤ ∑ e ∈ L.toFinset, (Tt e : ℝ) / (P.Q : ℝ) ^ P.K :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
      _ ≤ ∑ e ∈ L.toFinset, L.count e • ((Tt e : ℝ) / (P.Q : ℝ) ^ P.K) := by
          apply Finset.sum_le_sum
          intro e he
          have hc : 1 ≤ L.count e := List.count_pos_iff.mpr (List.mem_toFinset.mp he)
          rw [nsmul_eq_mul]
          have h0 : 0 ≤ (Tt e : ℝ) / (P.Q : ℝ) ^ P.K := by positivity
          have hc' : (1 : ℝ) ≤ L.count e := by exact_mod_cast hc
          nlinarith
      _ = (L.map (fun e => (Tt e : ℝ) / (P.Q : ℝ) ^ P.K)).sum := (Finset.sum_list_map_count L _).symm
      _ = ((L.map Tt).sum : ℝ) / (P.Q : ℝ) ^ P.K := by
          have hdiv : ∀ (M : List (ℕ × ℕ × ℕ)) (q : ℝ),
              (M.map (fun e => (Tt e : ℝ) / q)).sum = ((M.map Tt).sum : ℝ) / q := by
            intro M q
            induction M with
            | nil => simp
            | cons e M ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih, add_div]
          exact hdiv L _
  -- (4) the final inequality
  have hst_r : ((P.wE : ℝ) + P.wC) ^ 2 * ((L.map Tt).sum : ℝ) * P.K0d ≤
      P.K0n * P.Hmin * (P.Q : ℝ) ^ (P.K + 2) := by exact_mod_cast hst'
  calc (ωEof P + ωCof P) ^ 2 *
        ((∑ s ∈ (pats P.n P.K).filter (IsStK P t), wtW (ωEof P) (ωCof P) s * (HofK P t s : ℝ)) / P.Hmin)
      ≤ (ωEof P + ωCof P) ^ 2 * ((((L.map Tt).sum : ℝ) / (P.Q : ℝ) ^ P.K) / P.Hmin) := by
        gcongr
    _ = (((P.wE : ℝ) + P.wC) ^ 2 * ((L.map Tt).sum : ℝ)) / ((P.Q : ℝ) ^ (P.K + 2) * P.Hmin) := by
        unfold ωEof ωCof
        field_simp
        ring
    _ ≤ (P.K0n : ℝ) / P.K0d := by
        rw [div_le_div_iff₀ (by positivity) hKr]
        nlinarith [hst_r]

/-! ## Chunks -/

theorem rowsOKK_append {P : Params} {t : KTree} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : rowsOKK P t a b = true) (h2 : rowsOKK P t b c = true) : rowsOKK P t a c = true := by
  unfold rowsOKK at *
  have : (t.toList.drop a).take (c - a) = (t.toList.drop a).take (b - a) ++ (t.toList.drop b).take (c - b) := by
    rw [show c - a = (b - a) + (c - b) by omega, List.take_add, List.drop_drop, show a + (b - a) = b by omega]
  rw [this, List.all_append, h1, h2]
  rfl

theorem rowCheckK_of_rowsOKK {P : Params} {t : KTree} (h : rowsOKK P t 0 t.toList.length = true) :
    ∀ e ∈ t.toList, rowCheckK P t e = true := by
  unfold rowsOKK at h
  rw [List.drop_zero, Nat.sub_zero, List.take_length, List.all_eq_true] at h
  exact h

theorem dfsOKK_of_tops {P : Params} {t : KTree} (hK : 1 ≤ P.K)
    (h : ∀ j < (candList P.n).length, dfsTopK P t j = true) : dfsOKK P t P.K [] = true := by
  obtain ⟨r, hr⟩ : ∃ r, P.K = r + 1 := ⟨P.K - 1, by omega⟩
  rw [hr]
  simp only [dfsOKK, List.nil_append, List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := h j hj
  simp only [dfsTopK, List.getElem?_eq_getElem hj, hr, Nat.add_sub_cancel] at this
  exact this

end QEC
