import QEC.Count.CertSound
import QEC.Count.CountingX
import QECCountComp.Safe

/-!
# Soundness of the certificate checks with the SAFE rules (`QECCountComp/Safe.lean`)

`ExclS`: a window with two SAFE witnesses accepted by `checkWS`. From the SAFE checks (`rowCheckS` for every listed
state, `dfsOKS`, `startOK`) we get the hypotheses of `sum_legal_leX` with `X = ExclS`; `IsSt`, `Hof`, `ωEof`, `ωCof`,
`lamOf` are those of `CertSound.lean`. Also the chunk lemmas for the SAFE checks.

The proofs are those of `CertSound.lean`, with the SAFE functions in place of the FULL ones.
-/

namespace QEC

open Finset QECComp

/-- A window excluded by the SAFE rules: two witnesses pass `checkWS`. -/
def ExclS (n : ℕ) (c : List ℤ) (w : List (ℕ × Bool)) : Prop := ∃ W1 W2, checkWS n c w W1 W2 = true

namespace CertSoundS

/-- A SAFE witness pair contains a witness accepted by `checkW`. -/
theorem excl_of_exclS {n : ℕ} {c : List ℤ} {w : List (ℕ × Bool)} (h : ExclS n c w) : Excl n c w := by
  obtain ⟨W1, W2, hW⟩ := h
  unfold checkWS at hW
  simp only [Bool.and_eq_true] at hW
  exact ⟨W1, hW.1.1.1⟩

/-- A window of one edge is never SAFE-excluded. -/
theorem not_exclS_single {n : ℕ} {c : List ℤ} {x : ℕ × Bool} (hx : x.1 < 2 * n) : ¬ ExclS n c [x] :=
  fun h => CertSound.not_excl_single hx (excl_of_exclS h)

end CertSoundS

open CertSound CertSoundS

variable (P : Params) (keys Hs : Array ℕ)

theorem exclWinS_sound {u : List (ℕ × Bool)} (h : exclWinS P u = true) : ExclS P.n P.c u := by
  unfold exclWinS at h
  split at h
  · exact ⟨_, _, h⟩
  · exact absurd h (by simp)


/-- The contribution of the candidate `x` to the row of `s`. -/
def rcontribS (s : List (ℕ × Bool)) (x : ℕ × Bool) : ℕ :=
  if selfAvoid P.n (s ++ [x]) = true then
    match lookup keys (keyOf P.n (s ++ [x]).tail) with
    | some j => if exclWinS P (s ++ [x]) = true then 0 else (if x.2 then P.wC else P.wE) * Hs[j]!
    | none => 0
  else 0

/-- A candidate that is self-avoiding and leads to an unlisted state has an excluded window. -/
def rgoodS (s : List (ℕ × Bool)) (x : ℕ × Bool) : Prop :=
  selfAvoid P.n (s ++ [x]) = true → lookup keys (keyOf P.n (s ++ [x]).tail) = none → exclEndingS P (s ++ [x]) = true

theorem rowSumS_spec {s : List (ℕ × Bool)} {tot : ℕ} (h : rowSumS P keys Hs s = some tot) :
    tot = ((candList P.n).map (rcontribS P keys Hs s)).sum ∧ ∀ x ∈ candList P.n, rgoodS P keys s x := by
  unfold rowSumS at h
  have := foldl_opt _ (rcontribS P keys Hs s) (rgoodS P keys s) (fun x => rfl) ?_ ?_ (candList P.n) 0 tot h
  · simpa using this
  · intro a x hx
    simp only [rgoodS] at hx
    simp only [rcontribS]
    by_cases h1 : selfAvoid P.n (s ++ [x]) = true
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      cases h2 : lookup keys (keyOf P.n (s ++ [x]).tail) with
      | some j =>
        simp only
        by_cases h3 : exclWinS P (s ++ [x]) = true
        · simp [h3]
        · simp [h3]
      | none =>
        have h3 := hx h1 h2
        simp [h3]
    · simp only [Bool.not_eq_true] at h1
      simp [h1]
  · intro a x hx
    simp only [rgoodS, not_imp] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    simp only [Bool.not_eq_true] at h3
    simp [h1, h2, h3]

theorem rowCheckS_spec {i : ℕ} (h : rowCheckS P keys Hs i = true) :
    0 < P.Hmin ∧ P.Hmin ≤ Hs[i]! ∧ ∃ tot, rowSumS P keys Hs (decodeKey P.n P.K keys[i]!) = some tot ∧
      tot * P.lamD ≤ P.lamN * P.Q * Hs[i]! := by
  unfold rowCheckS at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · rename_i tot htot
    exact ⟨tot, htot, by simpa using h3⟩
  · exact absurd h3 (by simp)

theorem exclEndingS_sound {u : List (ℕ × Bool)} (h : exclEndingS P u = true) :
    ∃ m, 2 ≤ m ∧ m ≤ u.length ∧ m ≤ P.K + 1 ∧ ExclS P.n P.c (u.drop (u.length - m)) := by
  unfold exclEndingS at h
  rw [List.any_eq_true] at h
  obtain ⟨m, hm, hx⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [List.mem_range] at hm
  exact ⟨m, hx.1.1, hx.1.2, by omega, exclWinS_sound P hx.2⟩

theorem certS_pos (hrows : ∀ i < keys.size, rowCheckS P keys Hs i = true) :
    ∀ s, IsSt P keys s → P.Hmin ≤ Hof P keys Hs s := by
  intro s hs
  obtain ⟨j, hj, hjlt, -⟩ := isSt_lookup P keys hs
  rw [hof_of_lookup P keys Hs hj]
  exact (rowCheckS_spec P keys Hs (hrows j hjlt)).2.1

theorem certS_start (hn : 0 < P.n) (hdfs : dfsOKS P keys P.K [] = true) :
    ∀ s, s.length = P.K → LegalX P.n (ExclS P.n P.c) (P.K + 1) s → IsSt P keys s := by
  intro s hlen hleg
  obtain ⟨hsa, hdir, hwin⟩ := hleg
  have key : ∀ j, j ≤ P.K → dfsOKS P keys (P.K - j) (s.take j) = true := by
    intro j
    induction j with
    | zero => intro _; simpa using hdfs
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      rw [show P.K - j = (P.K - (j + 1)) + 1 by omega] at h1
      simp only [dfsOKS, List.all_eq_true] at h1
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
        obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingS_sound P hx
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
  simp only [dfsOKS] at hK
  exact ⟨hlen, hdir, hK⟩

theorem certS_closed (hn : 0 < P.n) (hrows : ∀ i < keys.size, rowCheckS P keys Hs i = true) :
    ∀ s, IsSt P keys s → ∀ x, SuccX P.n (ExclS P.n P.c) s x → IsSt P keys (s ++ [x]).tail := by
  intro s hs x hx
  obtain ⟨j, -, hjlt, hdec⟩ := isSt_decode P keys hn hs
  obtain ⟨-, -, tot, htot, -⟩ := rowCheckS_spec P keys Hs (hrows j hjlt)
  rw [hdec] at htot
  obtain ⟨-, hgood⟩ := rowSumS_spec P keys Hs htot
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
      obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingS_sound P (hg hsa hl)
      have hlenu : (s ++ [x]).length = s.length + 1 := by simp
      rw [hlenu] at hmle hex
      exact hx.2.2 m hm2 hmle hex

open scoped Classical in
theorem certS_rows (hn : 0 < P.n) (hQ : 0 < P.Q) (hlamD : 0 < P.lamD)
    (hrows : ∀ i < keys.size, rowCheckS P keys Hs i = true) :
    ∀ s, IsSt P keys s →
      ∑ x ∈ (cands P.n).filter (SuccX P.n (ExclS P.n P.c) s),
          wtW (ωEof P) (ωCof P) [x] * (Hof P keys Hs (s ++ [x]).tail : ℝ) ≤ lamOf P * Hof P keys Hs s := by
  intro s hs
  obtain ⟨j, hj, hjlt, hdec⟩ := isSt_decode P keys hn hs
  obtain ⟨-, -, tot, htot, hrow⟩ := rowCheckS_spec P keys Hs (hrows j hjlt)
  rw [hdec] at htot
  obtain ⟨htot_eq, -⟩ := rowSumS_spec P keys Hs htot
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hQ
  have hlamDr : (0 : ℝ) < P.lamD := by exact_mod_cast hlamD
  -- each successor's term is its contribution to the computed row, divided by `Q`
  have hterm : ∀ x ∈ (cands P.n).filter (SuccX P.n (ExclS P.n P.c) s),
      wtW (ωEof P) (ωCof P) [x] * (Hof P keys Hs (s ++ [x]).tail : ℝ) = (rcontribS P keys Hs s x : ℝ) / P.Q := by
    intro x hxm
    have hx := (Finset.mem_filter.mp hxm).2
    have hsa : selfAvoid P.n (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
    have hnex : exclWinS P (s ++ [x]) = false := by
      cases he : exclWinS P (s ++ [x])
      · rfl
      · exfalso
        have hE := exclWinS_sound P he
        by_cases hK : 1 ≤ s.length
        · exact hx.2.2 (s.length + 1) (by omega) le_rfl (by simpa using hE)
        · have hs0 : s = [] := List.length_eq_zero_iff.mp (by omega)
          subst hs0
          exact not_exclS_single hx.1 (by simpa using hE)
    obtain ⟨j', hj', -, -⟩ := isSt_lookup P keys (certS_closed P keys Hs hn hrows s hs x hx)
    rw [hof_of_lookup P keys Hs hj']
    simp only [rcontribS, hsa, ite_true, hj', hnex, Bool.false_eq_true, ite_false]
    unfold wtW ωEof ωCof
    obtain ⟨d, b⟩ := x
    cases b <;> simp [div_mul_eq_mul_div]
  have hsumC : ∑ x ∈ cands P.n, (rcontribS P keys Hs s x : ℝ) = (tot : ℝ) := by
    rw [cands_eq_toFinset, List.sum_toFinset _ (candList_nodup _), htot_eq]
    push_cast
    rw [List.map_map]
    rfl
  calc ∑ x ∈ (cands P.n).filter (SuccX P.n (ExclS P.n P.c) s), wtW (ωEof P) (ωCof P) [x] * (Hof P keys Hs (s ++ [x]).tail : ℝ)
      = ∑ x ∈ (cands P.n).filter (SuccX P.n (ExclS P.n P.c) s), (rcontribS P keys Hs s x : ℝ) / P.Q := Finset.sum_congr rfl hterm
    _ ≤ ∑ x ∈ cands P.n, (rcontribS P keys Hs s x : ℝ) / P.Q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (tot : ℝ) / P.Q := by rw [← Finset.sum_div, hsumC]
    _ ≤ lamOf P * Hof P keys Hs s := by
        rw [hof_of_lookup P keys Hs hj, lamOf, div_le_iff₀ hQr]
        have hrow' : (tot : ℝ) * P.lamD ≤ P.lamN * P.Q * (Hs[j]! : ℝ) := by exact_mod_cast hrow
        rw [show (P.lamN : ℝ) / P.lamD * (Hs[j]! : ℝ) * P.Q = (P.lamN * P.Q * (Hs[j]! : ℝ)) / P.lamD by ring,
          le_div_iff₀ hlamDr]
        exact hrow'

open scoped Classical in
theorem certS_startSum (hn : 0 < P.n) (hQ : 0 < P.Q) (hK0d : 0 < P.K0d) (hHmin : 0 < P.Hmin)
    (hst : startOK P keys Hs = true) :
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


/-! ## Chunks -/

theorem rowsOKS_append {P : Params} {keys Hs : Array ℕ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : rowsOKS P keys Hs a b = true) (h2 : rowsOKS P keys Hs b c = true) : rowsOKS P keys Hs a c = true := by
  unfold rowsOKS at *
  have : List.range' a (c - a) = List.range' a (b - a) ++ List.range' b (c - b) := by
    have h := List.range'_append_1 (s := a) (m := b - a) (n := c - b)
    rw [show a + (b - a) = b by omega, show b - a + (c - b) = c - a by omega] at h
    exact h.symm
  rw [this, List.all_append, h1, h2]
  rfl

theorem rowCheckS_of_rowsOKS {P : Params} {keys Hs : Array ℕ} {hi : ℕ} (h : rowsOKS P keys Hs 0 hi = true) :
    ∀ i < hi, rowCheckS P keys Hs i = true := by
  intro i hi'
  unfold rowsOKS at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'.mpr ⟨i, by omega, by simp⟩)

theorem dfsOKS_of_tops {P : Params} {keys : Array ℕ} (hK : 1 ≤ P.K)
    (h : ∀ j < (candList P.n).length, dfsTopS P keys j = true) : dfsOKS P keys P.K [] = true := by
  obtain ⟨r, hr⟩ : ∃ r, P.K = r + 1 := ⟨P.K - 1, by omega⟩
  rw [hr]
  simp only [dfsOKS, List.nil_append, List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := h j hj
  simp only [dfsTopS, List.getElem?_eq_getElem hj, hr, Nat.add_sub_cancel] at this
  exact this

end QEC
