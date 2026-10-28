import QEC.Count.CertSoundT
import QEC.Count.CertSoundK
import QECCountComp.KernT

/-!
# Soundness of the kernel seam checks (`QECCountComp/KernT.lean`)

The kernel route reaches the listed states through two lookups `fN fB` (near states by `nearKey σ o`, bulk states by
`keyOf 2 σ`), each returning (potential, mask), and checks the rows of the entries of two lists `eN eB` that contain
every value the lookups return (`memN`, `memB`; for a tree store, `find_mem`). `IsStTK`, `HofTK` are `IsStT`, `HofT`
with `potTK` in place of `potT`. From the checks (`CertOKTK`) we get the hypotheses of `sum_legal_leT` that
`CertSoundT.lean` gets from `CertOKT`: `certTK_pos`, `certTK_closed`, `certTK_rows`, `certTK_start`,
`certTK_startSum`. A mask is only a hint: a marked candidate with a listed target must be excluded (checked), an
unmarked listed candidate enters the computed row, so the computed row bounds the row of the legal successors.
-/

namespace QEC

open Finset QECComp SeamShift CertSound CertSoundT

section CertK

variable (P : ParamsT) (fN fB : ℕ → Option (ℕ × ℕ)) (eN eB : List (ℕ × ℕ × ℕ))

/-- The states of the kernel seam certificate on the torus of size `L`. -/
def IsStTK (L : ℕ) (s : List (ℕ × Bool)) (o : ℤ) : Prop :=
  qoffZ L o = o ∧ s.length = P.K ∧ DirOK 2 s ∧ (potTK P fN fB s (headOffT L s o)).isSome

/-- The potential of a state of the kernel seam certificate. -/
def HofTK (L : ℕ) (s : List (ℕ × Bool)) (o : ℤ) : ℕ :=
  ((potTK P fN fB s (headOffT L s o)).map Prod.fst).getD 0

/-- The checks of a kernel seam certificate (lookups `fN fB`, entries `eN eB`). -/
structure CertOKTK : Prop where
  memN : ∀ k h m, fN k = some (h, m) → (k, h, m) ∈ eN
  memB : ∀ k h m, fB k = some (h, m) → (k, h, m) ∈ eB
  hK : 1 ≤ P.K
  hHC : P.HC = 2 * P.K + 2
  hQ : 0 < P.Q
  hlamD : 0 < P.lamD
  near : ∀ e ∈ eN, nearRowTK P fN fB e = true
  bulk : ∀ e ∈ eB, bulkRowTK P fN fB e = true
  dfs : ∀ i, i ≤ 2 * (P.HC + P.K) → dfsTK P fN fB (offT P i) P.K [] = true
  start : startOKTK P (sumL (eN.map (nearContribT P))) (sumL (eB.map (bulkContribT P))) = true
  hK0d : 0 < P.K0d
  hHC2 : P.HC ≤ 2048

namespace CertSoundTK

/-! ## The computational checks, unfolded -/

theorem exclWinTK_sound {o : ℤ} {u : List (ℕ × Bool)} (h : exclWinTK P o u = true) : ExclT P.L0 o u := by
  unfold exclWinTK at h
  split at h
  · exact ⟨_, h⟩
  · exact absurd h (by simp)

theorem exclEndingTK_sound {o : ℤ} {u : List (ℕ × Bool)} (h : exclEndingTK P o u = true) :
    ∃ m, 2 ≤ m ∧ m ≤ u.length ∧ m ≤ P.K + 1 ∧
      ExclT P.L0 (o + xdisp (u.take (u.length - m))) (u.drop (u.length - m)) := by
  unfold exclEndingTK at h
  rw [List.any_eq_true] at h
  obtain ⟨m, hm, hx⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [List.mem_range] at hm
  exact ⟨m, hx.1.1, hx.1.2, by omega, exclWinTK_sound P hx.2⟩

theorem zip8_nodup : ((candList 2).zip (List.range 8)).Nodup := CertSoundK.zip_nodup 2

theorem mem_zip8 {x : ℕ × Bool} (hx : x ∈ candList 2) :
    (x, (candList 2).idxOf x) ∈ (candList 2).zip (List.range 8) := CertSoundK.mem_zip_idx hx

/-- The contribution of the candidate `xi` (step, index) to the computed row of `s` at head offset `o` with mask
`mask`. -/
def rcontribTK (mask : ℕ) (s : List (ℕ × Bool)) (o : ℤ) (xi : (ℕ × Bool) × ℕ) : ℕ :=
  if selfAvoid 2 (s ++ [xi.1]) = true then
    match potTK P fN fB (s ++ [xi.1]).tail (o + xdisp [xi.1]) with
    | some hm => if (mask / 2 ^ xi.2 % 2 == 1) = true then 0 else (if xi.1.2 then P.wC else P.wE) * hm.1
    | none => 0
  else 0

/-- A marked candidate with a listed target has a checked exclusion; a self-avoiding candidate with an unlisted
target has an excluded window. -/
def rgoodTK (mask : ℕ) (s : List (ℕ × Bool)) (o : ℤ) (xi : (ℕ × Bool) × ℕ) : Prop :=
  selfAvoid 2 (s ++ [xi.1]) = true →
    match potTK P fN fB (s ++ [xi.1]).tail (o + xdisp [xi.1]) with
    | some _ => (mask / 2 ^ xi.2 % 2 == 1) = true → exclWinTK P (o - xdisp s) (s ++ [xi.1]) = true
    | none => exclEndingTK P (o - xdisp s) (s ++ [xi.1]) = true

theorem rowSumTK_spec {mask : ℕ} {s : List (ℕ × Bool)} {o : ℤ} {tot : ℕ}
    (h : rowSumTK P fN fB mask s o = some tot) :
    tot = (((candList 2).zip (List.range 8)).map (rcontribTK P fN fB mask s o)).sum ∧
      ∀ xi ∈ (candList 2).zip (List.range 8), rgoodTK P fN fB mask s o xi := by
  unfold rowSumTK at h
  have := foldl_opt _ (rcontribTK P fN fB mask s o) (rgoodTK P fN fB mask s o) (fun x => rfl) ?_ ?_ _ 0 tot h
  · simpa using this
  · intro a xi hx
    simp only [rgoodTK] at hx
    simp only [rcontribTK]
    by_cases h1 : selfAvoid 2 (s ++ [xi.1]) = true
    · have hx1 := hx h1
      simp only [h1, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      cases h2 : potTK P fN fB (s ++ [xi.1]).tail (o + xdisp [xi.1]) with
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
    simp only [rgoodTK] at hx
    by_cases h1 : selfAvoid 2 (s ++ [xi.1]) = true
    · have hx' : ¬ (match potTK P fN fB (s ++ [xi.1]).tail (o + xdisp [xi.1]) with
          | some _ => (mask / 2 ^ xi.2 % 2 == 1) = true → exclWinTK P (o - xdisp s) (s ++ [xi.1]) = true
          | none => exclEndingTK P (o - xdisp s) (s ++ [xi.1]) = true) := fun h' => hx (fun _ => h')
      simp only [h1, Bool.not_true, Bool.false_eq_true, ite_false]
      cases h2 : potTK P fN fB (s ++ [xi.1]).tail (o + xdisp [xi.1]) with
      | some hm =>
        rw [h2] at hx'
        simp only [not_imp, Bool.not_eq_true] at hx'
        simp [hx'.1, hx'.2]
      | none =>
        rw [h2] at hx'
        simp only [Bool.not_eq_true] at hx'
        simp [hx']
    · exact absurd (fun h => absurd h h1) hx

theorem rowCheckTK_spec {mask : ℕ} {s : List (ℕ × Bool)} {o : ℤ} {hv : ℕ}
    (h : rowCheckTK P fN fB mask s o hv = true) :
    0 < P.Hmin ∧ P.Hmin ≤ hv ∧ ∃ tot, rowSumTK P fN fB mask s o = some tot ∧ tot * P.lamD ≤ P.lamN * P.Q * hv := by
  unfold rowCheckTK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · rename_i tot htot
    exact ⟨tot, htot, by simpa using h3⟩
  · exact absurd h3 (by simp)

theorem potTK_near {s : List (ℕ × Bool)} {h : ℤ} (h1 : -(P.HC : ℤ) ≤ h) (h2 : h < P.HC) :
    potTK P fN fB s h = fN (nearKey s h) := by
  unfold potTK
  rw [if_pos ⟨h1, h2⟩]

theorem potTK_far {s : List (ℕ × Bool)} {h : ℤ} (hf : ¬ (-(P.HC : ℤ) ≤ h ∧ h < P.HC)) :
    potTK P fN fB s h = fB (keyOf 2 s) := by
  unfold potTK
  rw [if_neg hf]

variable {P fN fB eN eB}

theorem K_leK (hc : CertOKTK P fN fB eN eB) : P.K ≤ 1023 := by
  have h1 := hc.hHC
  have h2 := hc.hHC2
  omega

/-! ## The three facts behind the rows -/

/-- The computed row of a listed state (with the mask of its entry), and its potential. -/
theorem row_of_isStTK (hc : CertOKTK P fN fB eN eB) {L : ℕ} {s : List (ℕ × Bool)} {o : ℤ}
    (hs : IsStTK P fN fB L s o) :
    P.Hmin ≤ HofTK P fN fB L s o ∧ ∃ mask tot, rowSumTK P fN fB mask s (ocOf P (headOffT L s o)) = some tot ∧
      tot * P.lamD ≤ P.lamN * P.Q * HofTK P fN fB L s o := by
  obtain ⟨-, hlen, hdir, hpot⟩ := hs
  unfold HofTK
  generalize headOffT L s o = h at hpot ⊢
  have hHC2 := hc.hHC2
  by_cases hn : -(P.HC : ℤ) ≤ h ∧ h < P.HC
  · rw [potTK_near P fN fB hn.1 hn.2] at hpot ⊢
    obtain ⟨⟨hv, m⟩, hf⟩ := Option.isSome_iff_exists.mp hpot
    have hrow := hc.near _ (hc.memN _ _ _ hf)
    unfold nearRowTK at hrow
    obtain ⟨hd1, hd2⟩ := nearKey_decode hlen hdir (h := h) (by omega) (by omega)
    simp only at hrow
    rw [hd1, hd2] at hrow
    have hoc : ocOf P h = h := by unfold ocOf; rw [if_pos ⟨by omega, by omega⟩]
    rw [hoc, hf]
    obtain ⟨-, h2, tot, h3, h4⟩ := rowCheckTK_spec P fN fB hrow
    exact ⟨h2, m, tot, h3, h4⟩
  · rw [potTK_far P fN fB hn] at hpot ⊢
    obtain ⟨⟨hv, m⟩, hf⟩ := Option.isSome_iff_exists.mp hpot
    have hrow := hc.bulk _ (hc.memB _ _ _ hf)
    unfold bulkRowTK at hrow
    simp only [Bool.and_eq_true] at hrow
    obtain ⟨⟨hr1, hr2⟩, hr3⟩ := hrow
    rw [decodeKey_keyOf (by norm_num) P.K s hlen hdir] at hr1 hr2 hr3
    rw [hf]
    simp only [Option.map_some, Option.getD_some]
    unfold ocOf
    by_cases hsm : -(P.HC : ℤ) - 1 ≤ h ∧ h ≤ P.HC
    · rw [if_pos hsm]
      rcases (show h = P.HC ∨ h = -(P.HC : ℤ) - 1 by omega) with rfl | rfl
      · obtain ⟨-, h2, tot, h3, h4⟩ := rowCheckTK_spec P fN fB hr2
        exact ⟨h2, _, tot, h3, h4⟩
      · obtain ⟨-, h2, tot, h3, h4⟩ := rowCheckTK_spec P fN fB hr3
        exact ⟨h2, _, tot, h3, h4⟩
    · rw [if_neg hsm]
      obtain ⟨-, h2, tot, h3, h4⟩ := rowCheckTK_spec P fN fB hr1
      exact ⟨h2, _, tot, h3, h4⟩

/-- The exclusions of the windows of a successor agree at the offsets of the computed row and at the true
offsets (as `win_equiv`). -/
theorem win_equivK (hc : CertOKTK P fN fB eN eB) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L) {s : List (ℕ × Bool)}
    {o : ℤ} (ho : qoffZ L o = o) (hlen : s.length = P.K) (x : ℕ × Bool) {j : ℕ} (hj : j < P.K) :
    ExclT P.L0 (ocOf P (headOffT L s o) - xdisp s + xdisp ((s ++ [x]).take j)) ((s ++ [x]).drop j) ↔
      ExclT P.L0 (offAt (nxtT L) o (s ++ [x]) j) ((s ++ [x]).drop j) := by
  have hL0 : 0 < L := by omega
  have hLz : (4 * ((P.HC : ℤ) + P.K) + 4 : ℤ) ≤ L := by exact_mod_cast hL
  have hHC : (P.HC : ℤ) = 2 * P.K + 2 := by exact_mod_cast hc.hHC
  have hK1 : (1 : ℤ) ≤ P.K := by exact_mod_cast hc.hK
  have hK2 : (P.K : ℤ) ≤ 1023 := by exact_mod_cast K_leK hc
  have hb := renorm_bounds hL0 ho
  have hxs := xdisp_bounds s
  rw [hlen] at hxs
  have hulen : (s ++ [x]).length = P.K + 1 := by simp [hlen]
  have huK : (s ++ [x]).take P.K = s := by
    rw [← hlen]
    exact List.take_left' rfl
  rw [offAt_nxtT ho]
  have hxj := xdisp_take_bounds (s ++ [x]) j
  unfold ocOf
  by_cases hsm : -(P.HC : ℤ) - 1 ≤ headOffT L s o ∧ headOffT L s o ≤ P.HC
  · have hex := head_exact hL ho hlen hsm.1 hsm.2
    have hsm' := hsm
    rw [hex] at hsm'
    rw [if_pos hsm, hex]
    rw [qoffZ_of_bounds hL0 (by omega) (by omega)]
    ring_nf
  · rw [if_neg hsm]
    apply exclT_shift
    · apply oneSide_right
      intro i hi
      have hi' : j + i ≤ P.K + 1 := by rw [List.length_drop, hulen] at hi; omega
      have e := xdisp_take_add (s ++ [x]) j i
      have hb2 := xdisp_take_bounds (s ++ [x]) (j + i)
      unfold bigO
      push_cast at hb2
      omega
    · have hδ := xdisp_take_bounds ((s ++ [x]).drop j) (P.K - j)
      apply oneSide_of_ref hL0 (δ := xdisp (((s ++ [x]).drop j).take (P.K - j))) (E := P.K)
      · intro i hi
        have hi' : j + i ≤ P.K + 1 := by rw [List.length_drop, hulen] at hi; omega
        have e1 := xdisp_take_add (s ++ [x]) j i
        have e2 := xdisp_take_add (s ++ [x]) j (P.K - j)
        rw [show j + (P.K - j) = P.K by omega, huK] at e2
        rcases le_total (j + i) P.K with hle | hle
        · have := xdisp_take_sub (s ++ [x]) hle
          rw [huK] at this
          push_cast [Nat.cast_sub hle] at this
          constructor <;> omega
        · have := xdisp_take_sub (s ++ [x]) hle
          rw [huK] at this
          push_cast [Nat.cast_sub hle] at this
          constructor <;> omega
      · omega
      · have := qoffZ_bounds hL0 (o + xdisp ((s ++ [x]).take j))
        omega
      · have := qoffZ_bounds hL0 (o + xdisp ((s ++ [x]).take j))
        omega
      · rw [qoffZ_add, add_assoc, xdisp_take_add, show j + (P.K - j) = P.K by omega, huK, ← headOffT_eq ho]
        omega

/-- The potential of a successor at the offset of the computed row is its true potential (as `pot_succ`). -/
theorem pot_succK (hc : CertOKTK P fN fB eN eB) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L) {s : List (ℕ × Bool)}
    {o : ℤ} (ho : qoffZ L o = o) (hlen : s.length = P.K) (x : ℕ × Bool) :
    potTK P fN fB (s ++ [x]).tail (ocOf P (headOffT L s o) + xdisp [x]) =
      potTK P fN fB (s ++ [x]).tail (headOffT L (s ++ [x]).tail (offAt (nxtT L) o s 1)) := by
  have hL0 : 0 < L := by omega
  have hLz : (4 * ((P.HC : ℤ) + P.K) + 4 : ℤ) ≤ L := by exact_mod_cast hL
  have hK1 := hc.hK
  have hHC : (P.HC : ℤ) = 2 * P.K + 2 := by exact_mod_cast hc.hHC
  have hK2 : (P.K : ℤ) ≤ 1023 := by exact_mod_cast K_leK hc
  have hs0 : s ≠ [] := by rintro rfl; simp at hlen; omega
  rw [headOffT_next ho hs0, xdisp_single]
  have hdx := dxOf_bounds x.1
  have hh := qoffZ_bounds hL0 (o + xdisp s)
  rw [← headOffT_eq ho] at hh
  unfold ocOf
  by_cases hsm : -(P.HC : ℤ) - 1 ≤ headOffT L s o ∧ headOffT L s o ≤ P.HC
  · rw [if_pos hsm, qoffZ_of_bounds hL0 (by omega) (by omega)]
  · rw [if_neg hsm, potTK_far P fN fB (by unfold bigO; omega)]
    rcases qoffZ_cases hL0 (b := headOffT L s o + dxOf x.1) (by omega) (by omega) with ⟨-, -, c⟩ | ⟨c1, c2⟩ |
      ⟨c1, c2⟩
    · rw [potTK_far P fN fB (by rw [c]; omega)]
    · rw [potTK_far P fN fB (by rw [c2]; omega)]
    · rw [potTK_far P fN fB (by rw [c2]; omega)]

end CertSoundTK

open CertSoundTK

variable {P fN fB eN eB}

/-! ## Positivity, closure and rows -/

theorem certTK_pos (hc : CertOKTK P fN fB eN eB) {L : ℕ} {s : List (ℕ × Bool)} {o : ℤ}
    (hs : IsStTK P fN fB L s o) : P.Hmin ≤ HofTK P fN fB L s o :=
  (row_of_isStTK hc hs).1

theorem certTK_closed (hc : CertOKTK P fN fB eN eB) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L)
    {s : List (ℕ × Bool)} {o : ℤ} (hs : IsStTK P fN fB L s o) {x : ℕ × Bool}
    (hx : SuccG (nxtT L) (ExclT P.L0) s o x) :
    IsStTK P fN fB L (s ++ [x]).tail (offAt (nxtT L) o s 1) := by
  have hs' := hs
  obtain ⟨ho, hlen, hdir, -⟩ := hs
  obtain ⟨-, mask, tot, htot, -⟩ := row_of_isStTK hc hs'
  obtain ⟨-, hgood⟩ := rowSumTK_spec P fN fB htot
  have hx1 : x.1 < 2 * 2 := hx.1
  have hg := hgood (x, (candList 2).idxOf x) (mem_zip8 (mem_candList.mpr hx1))
  have hsa : selfAvoid 2 (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [offAt_nxtT ho]
    exact qoffZ_idem _
  · simp [hlen]
  · intro y hy
    rcases List.mem_append.mp (List.mem_of_mem_tail hy) with hy | hy
    · exact hdir y hy
    · rw [List.mem_singleton.mp hy]
      exact hx1
  · rw [← pot_succK hc hL ho hlen x]
    cases hp : potTK P fN fB (s ++ [x]).tail (ocOf P (headOffT L s o) + xdisp [x]) with
    | some _ => rfl
    | none =>
      exfalso
      have hg' := hg hsa
      simp only at hg'
      rw [hp] at hg'
      obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingTK_sound P hg'
      have hulen : (s ++ [x]).length = s.length + 1 := by simp
      rw [hulen] at hmle hex
      have hj : s.length + 1 - m < P.K := by omega
      rw [win_equivK hc hL ho hlen x hj] at hex
      exact hx.2.2 m hm2 hmle hex

open scoped Classical in
theorem certTK_rows (hc : CertOKTK P fN fB eN eB) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L)
    {s : List (ℕ × Bool)} {o : ℤ} (hs : IsStTK P fN fB L s o) :
    ∑ x ∈ (cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
        (HofTK P fN fB L (s ++ [x]).tail (offAt (nxtT L) o s 1) : ℝ) ≤
      ((P.lamN : ℝ) / P.lamD) * HofTK P fN fB L s o := by
  have hs' := hs
  obtain ⟨ho, hlen, hdir, -⟩ := hs
  have hK1 := hc.hK
  obtain ⟨-, mask, tot, htot, hrow⟩ := row_of_isStTK hc hs'
  obtain ⟨htot_eq, hgood⟩ := rowSumTK_spec P fN fB htot
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hc.hQ
  have hlamDr : (0 : ℝ) < P.lamD := by exact_mod_cast hc.hlamD
  set Z := (candList 2).zip (List.range 8) with hZ
  set oc := ocOf P (headOffT L s o) with hoc
  let f : ℕ × Bool → (ℕ × Bool) × ℕ := fun x => (x, (candList 2).idxOf x)
  have hterm : ∀ x ∈ (cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
        (HofTK P fN fB L (s ++ [x]).tail (offAt (nxtT L) o s 1) : ℝ) =
      (rcontribTK P fN fB mask s oc (f x) : ℝ) / P.Q := by
    intro x hxm
    have hx := (Finset.mem_filter.mp hxm).2
    have hsa : selfAvoid 2 (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
    obtain ⟨-, -, -, hp⟩ := certTK_closed hc hL hs' hx
    obtain ⟨⟨h', m'⟩, hh'⟩ := Option.isSome_iff_exists.mp hp
    have hps : potTK P fN fB (s ++ [x]).tail (oc + xdisp [x]) =
        potTK P fN fB (s ++ [x]).tail (headOffT L (s ++ [x]).tail (offAt (nxtT L) o s 1)) :=
      pot_succK hc hL ho hlen x
    have hg := hgood (f x) (mem_zip8 (mem_candList.mpr hx.1)) hsa
    simp only [f] at hg
    rw [hps, hh'] at hg
    have hbit : (mask / 2 ^ (candList 2).idxOf x % 2 == 1) = false := by
      cases hb : (mask / 2 ^ (candList 2).idxOf x % 2 == 1)
      · rfl
      · exfalso
        have hE := exclWinTK_sound P (hg hb)
        have hw := win_equivK hc hL ho hlen x hc.hK
        simp only [List.take_zero, xdisp_nil, add_zero, List.drop_zero] at hw
        rw [hw] at hE
        exact hx.2.2 (s.length + 1) (by omega) le_rfl (by simpa using hE)
    have hHof : HofTK P fN fB L (s ++ [x]).tail (offAt (nxtT L) o s 1) = h' := by
      unfold HofTK
      rw [hh']
      rfl
    rw [hHof]
    simp only [rcontribTK, f, hsa, ite_true, hps, hh', hbit, Bool.false_eq_true, ite_false]
    unfold wtW
    obtain ⟨d, b⟩ := x
    cases b <;> simp [div_mul_eq_mul_div]
  have hinj : Set.InjOn f ↑((cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o)) := by
    intro x _ y _ hxy
    exact (Prod.mk.inj hxy).1
  have himg : ((cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o)).image f ⊆ Z.toFinset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [List.mem_toFinset]
    exact mem_zip8 (mem_candList.mpr (Finset.mem_filter.mp hx).2.1)
  have hsumZ : ∑ y ∈ Z.toFinset, (rcontribTK P fN fB mask s oc y : ℝ) = (tot : ℝ) := by
    rw [List.sum_toFinset _ zip8_nodup, htot_eq]
    push_cast
    rw [List.map_map]
    rfl
  calc ∑ x ∈ (cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o),
        wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
          (HofTK P fN fB L (s ++ [x]).tail (offAt (nxtT L) o s 1) : ℝ)
      = ∑ x ∈ (cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o),
          (rcontribTK P fN fB mask s oc (f x) : ℝ) / P.Q := Finset.sum_congr rfl hterm
    _ = ∑ y ∈ ((cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o)).image f,
          (rcontribTK P fN fB mask s oc y : ℝ) / P.Q :=
        (Finset.sum_image (f := fun y => (rcontribTK P fN fB mask s oc y : ℝ) / P.Q) hinj).symm
    _ ≤ ∑ y ∈ Z.toFinset, (rcontribTK P fN fB mask s oc y : ℝ) / P.Q :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
    _ = (tot : ℝ) / P.Q := by rw [← Finset.sum_div, hsumZ]
    _ ≤ ((P.lamN : ℝ) / P.lamD) * HofTK P fN fB L s o := by
        rw [div_le_iff₀ hQr]
        have hrow' : (tot : ℝ) * P.lamD ≤ P.lamN * P.Q * (HofTK P fN fB L s o : ℝ) := by exact_mod_cast hrow
        rw [show (P.lamN : ℝ) / P.lamD * (HofTK P fN fB L s o : ℝ) * P.Q =
          (P.lamN * P.Q * (HofTK P fN fB L s o : ℝ)) / P.lamD by ring, le_div_iff₀ hlamDr]
        exact hrow'

/-! ## Start completeness -/

namespace CertSoundTK

/-- The start offset of index `(o + HC + K).toNat` is `o`, for `o` near the seam. -/
theorem offT_idx {o : ℤ} (h1 : -((P.HC + P.K : ℕ) : ℤ) ≤ o) (h2 : o < ((P.HC + P.K : ℕ) : ℤ)) :
    (o + ((P.HC + P.K : ℕ) : ℤ)).toNat ≤ 2 * (P.HC + P.K) ∧ offT P (o + ((P.HC + P.K : ℕ) : ℤ)).toNat = o := by
  refine ⟨by omega, ?_⟩
  unfold offT
  rw [if_pos (by omega)]
  omega

/-- The last start offset is `bigO`. -/
theorem offT_big : offT P (2 * (P.HC + P.K)) = bigO := by
  unfold offT
  rw [if_neg (by omega)]

/-- Start completeness from the check `dfsTK` at `o0`, for a pattern whose exclusions at the offsets
`o0 + xdisp (s.take i)` imply its exclusions at its true offsets (as `start_of_dfs`). -/
theorem start_of_dfsK {L : ℕ} {o o0 : ℤ} {s : List (ℕ × Bool)} (hK : 1 ≤ P.K) (hlen : s.length = P.K)
    (hdfs : dfsTK P fN fB o0 P.K [] = true) (hleg : LegalG (nxtT L) (ExclT P.L0) (P.K + 1) o s)
    (hwin : ∀ i m, 2 ≤ m → i + m ≤ P.K → ExclT P.L0 (o0 + xdisp (s.take i)) ((s.drop i).take m) →
      ExclT P.L0 (offAt (nxtT L) o s i) ((s.drop i).take m)) :
    (potTK P fN fB s (o0 + xdisp s)).isSome = true := by
  obtain ⟨hsa, hdir, hw⟩ := hleg
  have key : ∀ j, j ≤ P.K → dfsTK P fN fB o0 (P.K - j) (s.take j) = true := by
    intro j
    induction j with
    | zero => intro _; simpa using hdfs
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      rw [show P.K - j = (P.K - (j + 1)) + 1 by omega] at h1
      simp only [dfsTK, List.all_eq_true] at h1
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
      · exact hx
      · exfalso
        obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingTK_sound P hx
        rw [hlt] at hmle hex
        have hw1 : (s.take (j + 1)).drop (j + 1 - m) = (s.drop (j + 1 - m)).take m := by
          rw [List.drop_take]
          congr 1
          omega
        have hw2 : (s.take (j + 1)).take (j + 1 - m) = s.take (j + 1 - m) := by
          rw [List.take_take]
          congr 1
          omega
        rw [hw1, hw2] at hex
        exact hw (j + 1 - m) m hm2 (by omega) (by omega) (hwin _ _ hm2 (by omega) hex)
  have hK' := key P.K le_rfl
  rw [Nat.sub_self, List.take_of_length_le (by omega)] at hK'
  simpa only [dfsTK] using hK'

end CertSoundTK

theorem certTK_start (hc : CertOKTK P fN fB eN eB) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L) {o : ℤ}
    (ho : qoffZ L o = o) {s : List (ℕ × Bool)} (hs : s.length = P.K)
    (hleg : LegalG (nxtT L) (ExclT P.L0) (P.K + 1) o s) : IsStTK P fN fB L s o := by
  refine ⟨ho, hs, hleg.2.1, ?_⟩
  have hL0 : 0 < L := by omega
  have hLz : (4 * ((P.HC : ℤ) + P.K) + 4 : ℤ) ≤ L := by exact_mod_cast hL
  have hHC : (P.HC : ℤ) = 2 * P.K + 2 := by exact_mod_cast hc.hHC
  have hK2 : (P.K : ℤ) ≤ 1023 := by exact_mod_cast K_leK hc
  have hb := renorm_bounds hL0 ho
  have hxs := xdisp_bounds s
  rw [hs] at hxs
  by_cases hn : -((P.HC + P.K : ℕ) : ℤ) ≤ o ∧ o < ((P.HC + P.K : ℕ) : ℤ)
  · -- a start near the seam: the check `dfsTK` at `o`, no wrap-around
    obtain ⟨hi, hoff⟩ := offT_idx hn.1 hn.2
    have hd := hc.dfs _ hi
    rw [hoff] at hd
    push_cast at hn
    have hwin : ∀ i m, 2 ≤ m → i + m ≤ P.K → ExclT P.L0 (o + xdisp (s.take i)) ((s.drop i).take m) →
        ExclT P.L0 (offAt (nxtT L) o s i) ((s.drop i).take m) := by
      intro i m _ him hE
      have hxi := xdisp_take_bounds s i
      rw [offAt_nxtT ho, qoffZ_of_bounds hL0 (by omega) (by omega)]
      exact hE
    have := start_of_dfsK hc.hK hs hd hleg hwin
    rw [headOffT_eq ho, qoffZ_of_bounds hL0 (by omega) (by omega)]
    exact this
  · -- a start far from the seam: the check `dfsTK` at `bigO`, by translation
    have hd := hc.dfs (2 * (P.HC + P.K)) le_rfl
    rw [offT_big] at hd
    push_cast at hn
    have hwin : ∀ i m, 2 ≤ m → i + m ≤ P.K → ExclT P.L0 (bigO + xdisp (s.take i)) ((s.drop i).take m) →
        ExclT P.L0 (offAt (nxtT L) o s i) ((s.drop i).take m) := by
      intro i m _ him hE
      have hwl : ((s.drop i).take m).length ≤ m := List.length_take_le _ _
      have hpre : ∀ k ≤ ((s.drop i).take m).length,
          xdisp (((s.drop i).take m).take k) = xdisp (s.take (i + k)) - xdisp (s.take i) := by
        intro k hk
        rw [List.take_take, show min k m = k by omega, ← xdisp_take_add s i k]
        ring
      refine (exclT_shift ?_ ?_).mp hE
      · apply oneSide_right
        intro k hk
        rw [hpre k hk]
        have := xdisp_take_bounds s (i + k)
        unfold bigO
        push_cast at this
        omega
      · rw [offAt_nxtT ho]
        have hxi := xdisp_take_bounds s i
        apply oneSide_of_ref hL0 (δ := -xdisp (s.take i)) (E := P.K)
        · intro k hk
          rw [hpre k hk]
          have := xdisp_take_bounds s (i + k)
          push_cast at this
          constructor <;> omega
        · omega
        · have := qoffZ_bounds hL0 (o + xdisp (s.take i))
          omega
        · have := qoffZ_bounds hL0 (o + xdisp (s.take i))
          omega
        · rw [qoffZ_add, add_neg_cancel_right, ho]
          omega
    have := start_of_dfsK hc.hK hs hd hleg hwin
    rw [potTK_far P fN fB (by unfold bigO; omega)] at this
    rw [headOffT_eq ho]
    rcases qoffZ_cases hL0 (b := o + xdisp s) (by omega) (by omega) with ⟨-, -, c⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩
    · rw [c, potTK_far P fN fB (by omega)]
      exact this
    · rw [c2, potTK_far P fN fB (by omega)]
      exact this
    · rw [c2, potTK_far P fN fB (by omega)]
      exact this

/-! ## The start sum -/

namespace CertSoundTK

theorem getD_addL : ∀ (a b : List ℕ) (i : ℕ), (addL a b).getD i 0 = a.getD i 0 + b.getD i 0
  | [], b, i => by simp [addL]
  | x :: xs, [], i => by simp [addL]
  | x :: xs, y :: ys, i => by
    cases i with
    | zero => simp [addL]
    | succ i =>
      rw [show addL (x :: xs) (y :: ys) = (x + y) :: addL xs ys from rfl, List.getD_cons_succ,
        List.getD_cons_succ, List.getD_cons_succ]
      exact getD_addL xs ys i

theorem getD_sumL {α : Type*} (g : α → List ℕ) (i : ℕ) :
    ∀ l : List α, (sumL (l.map g)).getD i 0 = (l.map (fun e => (g e).getD i 0)).sum
  | [] => by simp [sumL]
  | e :: l => by
    rw [List.map_cons, List.map_cons, List.sum_cons,
      show sumL (g e :: l.map g) = addL (g e) (sumL (l.map g)) from rfl, getD_addL, getD_sumL g i l]

theorem getD_map_range (n : ℕ) (F : ℕ → ℕ) {i : ℕ} (hi : i < n) :
    ((List.range n).map F).getD i 0 = F i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- A sum over the distinct entries of a list is at most the sum over the list. -/
theorem sum_toFinset_le_list {α : Type*} [DecidableEq α] (l : List α) (g : α → ℕ) :
    ∑ x ∈ l.toFinset, g x ≤ (l.map g).sum := by
  rw [Finset.sum_list_map_count]
  apply Finset.sum_le_sum
  intro x hx
  have : 1 ≤ l.count x := List.count_pos_iff.mpr (List.mem_toFinset.mp hx)
  rw [smul_eq_mul]
  exact Nat.le_mul_of_pos_left _ this

theorem nearContribT_getD {e : ℕ × ℕ × ℕ} {i : ℕ} (hi : i ≤ 2 * (P.HC + P.K)) :
    (nearContribT P e).getD i 0 =
      if (((e.1 % 4096 : ℕ) : ℤ) - 2048) - xdisp (decodeKey 2 P.K (e.1 / 4096)) == offT P i then
        wtT P (decodeKey 2 P.K (e.1 / 4096)) * e.2.1 else 0 := by
  unfold nearContribT
  exact getD_map_range _ _ (by omega)

theorem bulkContribT_getD {e : ℕ × ℕ × ℕ} {i : ℕ} (hi : i ≤ 2 * (P.HC + P.K)) :
    (bulkContribT P e).getD i 0 =
      if -(P.HC : ℤ) ≤ offT P i + xdisp (decodeKey 2 P.K e.1) ∧ offT P i + xdisp (decodeKey 2 P.K e.1) < P.HC
      then 0 else wtT P (decodeKey 2 P.K e.1) * e.2.1 := by
  unfold bulkContribT
  exact getD_map_range _ _ (by omega)

end CertSoundTK

open scoped Classical in
theorem certTK_startSum (hc : CertOKTK P fN fB eN eB) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L) {o : ℤ}
    (ho : qoffZ L o = o) :
    ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) *
      ∑ s ∈ (pats 2 P.K).filter (fun s => IsStTK P fN fB L s o),
        wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) s * (HofTK P fN fB L s o : ℝ) ≤
      ((P.K0n : ℝ) / P.K0d) * P.Hmin := by
  have hHC2 := hc.hHC2
  have hK2 : (P.K : ℤ) ≤ 1023 := by exact_mod_cast K_leK hc
  -- the index of the start check
  let near : Prop := -((P.HC + P.K : ℕ) : ℤ) ≤ o ∧ o < ((P.HC + P.K : ℕ) : ℤ)
  let i0 : ℕ := if near then (o + ((P.HC + P.K : ℕ) : ℤ)).toNat else 2 * (P.HC + P.K)
  let o0 : ℤ := if near then o else bigO
  have hi0 : i0 ≤ 2 * (P.HC + P.K) ∧ offT P i0 = o0 := by
    by_cases hn : near
    · simp only [i0, o0, if_pos hn]
      exact offT_idx hn.1 hn.2
    · simp only [i0, o0, if_neg hn]
      exact ⟨le_rfl, offT_big⟩
  have hst : (P.wE + P.wC) * ((sumL (eN.map (nearContribT P))).getD i0 0 +
      (sumL (eB.map (bulkContribT P))).getD i0 0) * P.K0d ≤ P.K0n * P.Hmin * P.Q ^ (P.K + 1) := by
    have h := hc.start
    unfold startOKTK at h
    rw [List.all_eq_true] at h
    have := h i0 (List.mem_range.mpr (by omega))
    simpa using this
  -- (1) the bound in integers, state by state
  have hnat : ∑ s ∈ (pats 2 P.K).filter (fun s => IsStTK P fN fB L s o),
      wtN P s * HofTK P fN fB L s o ≤
        (sumL (eN.map (nearContribT P))).getD i0 0 + (sumL (eB.map (bulkContribT P))).getD i0 0 := by
    rw [getD_sumL, getD_sumL, ← Finset.sum_filter_add_sum_filter_not _
      (fun s => -(P.HC : ℤ) ≤ headOffT L s o ∧ headOffT L s o < P.HC)]
    apply add_le_add
    · -- near heads: the near entries
      refine le_trans ?_ (sum_toFinset_le_list eN _)
      apply Finset.sum_le_sum_of_injOn
        (fun s => (nearKey s (headOffT L s o), (fN (nearKey s (headOffT L s o))).getD (0, 0)))
      · intro s hs t ht hst'
        simp only [Finset.mem_coe, Finset.mem_filter] at hs ht
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨⟨-, htS⟩, htn⟩ := ht
        obtain ⟨-, hslen, hsdir, -⟩ := hsS
        obtain ⟨-, htlen, htdir, -⟩ := htS
        have hk := congrArg Prod.fst hst'
        simp only at hk
        have e1 := (nearKey_decode hslen hsdir (h := headOffT L s o) (by omega) (by omega)).1
        have e2 := (nearKey_decode htlen htdir (h := headOffT L t o) (by omega) (by omega)).1
        rw [hk] at e1
        exact e1.symm.trans e2
      · intro j hj
        simp only [Finset.mem_image, Finset.mem_filter] at hj
        obtain ⟨s, ⟨⟨-, hsS⟩, hsn⟩, rfl⟩ := hj
        obtain ⟨-, -, -, hsp⟩ := hsS
        rw [potTK_near P fN fB hsn.1 hsn.2] at hsp
        obtain ⟨⟨hv, m⟩, hf⟩ := Option.isSome_iff_exists.mp hsp
        simp only [List.mem_toFinset, hf, Option.getD_some]
        exact hc.memN _ _ _ hf
      · intro s hs
        simp only [Finset.mem_filter] at hs
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨-, hslen, hsdir, hsp⟩ := hsS
        have hsp' := hsp
        rw [potTK_near P fN fB hsn.1 hsn.2] at hsp'
        obtain ⟨⟨hv, m⟩, hf⟩ := Option.isSome_iff_exists.mp hsp'
        obtain ⟨d1, d2⟩ := nearKey_decode hslen hsdir (h := headOffT L s o) (by omega) (by omega)
        simp only [hf, Option.getD_some]
        rw [nearContribT_getD hi0.1]
        simp only
        rw [d1, d2, hi0.2]
        have hcond : headOffT L s o - xdisp s = o0 := by
          by_cases hn : near
          · simp only [o0, if_pos hn]
            rw [head_exact_start hL ho hslen hn]
            ring
          · exact absurd hsn (head_far_start hL ho hslen hn)
        rw [if_pos (beq_iff_eq.mpr hcond)]
        apply le_of_eq
        unfold HofTK
        rw [potTK_near P fN fB hsn.1 hsn.2, hf]
        rfl
      · intro _ _ _
        exact Nat.zero_le _
    · -- far heads: the bulk entries
      refine le_trans ?_ (sum_toFinset_le_list eB _)
      apply Finset.sum_le_sum_of_injOn (fun s => (keyOf 2 s, (fB (keyOf 2 s)).getD (0, 0)))
      · intro s hs t ht hst'
        simp only [Finset.mem_coe, Finset.mem_filter] at hs ht
        obtain ⟨⟨-, hsS⟩, -⟩ := hs
        obtain ⟨⟨-, htS⟩, -⟩ := ht
        obtain ⟨-, hslen, hsdir, -⟩ := hsS
        obtain ⟨-, htlen, htdir, -⟩ := htS
        have hk := congrArg Prod.fst hst'
        simp only at hk
        exact keyOf_inj (by norm_num) hslen htlen hsdir htdir hk
      · intro j hj
        simp only [Finset.mem_image, Finset.mem_filter] at hj
        obtain ⟨s, ⟨⟨-, hsS⟩, hsn⟩, rfl⟩ := hj
        obtain ⟨-, -, -, hsp⟩ := hsS
        rw [potTK_far P fN fB hsn] at hsp
        obtain ⟨⟨hv, m⟩, hf⟩ := Option.isSome_iff_exists.mp hsp
        simp only [List.mem_toFinset, hf, Option.getD_some]
        exact hc.memB _ _ _ hf
      · intro s hs
        simp only [Finset.mem_filter] at hs
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨-, hslen, hsdir, hsp⟩ := hsS
        have hsp' := hsp
        rw [potTK_far P fN fB hsn] at hsp'
        obtain ⟨⟨hv, m⟩, hf⟩ := Option.isSome_iff_exists.mp hsp'
        simp only [hf, Option.getD_some]
        rw [bulkContribT_getD hi0.1]
        simp only
        rw [decodeKey_keyOf (by norm_num) P.K s hslen hsdir, hi0.2]
        have hcond : ¬ (-(P.HC : ℤ) ≤ o0 + xdisp s ∧ o0 + xdisp s < P.HC) := by
          by_cases hn : near
          · simp only [o0, if_pos hn]
            rw [← head_exact_start hL ho hslen hn]
            exact hsn
          · simp only [o0, if_neg hn]
            have hxs := xdisp_bounds s
            rw [hslen] at hxs
            unfold bigO
            omega
        rw [if_neg hcond]
        apply le_of_eq
        unfold HofTK
        rw [potTK_far P fN fB hsn, hf]
        rfl
      · intro _ _ _
        exact Nat.zero_le _
  -- (2) in reals
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hc.hQ
  have hKr : (0 : ℝ) < P.K0d := by exact_mod_cast hc.hK0d
  have hreal : ∑ s ∈ (pats 2 P.K).filter (fun s => IsStTK P fN fB L s o),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) s * (HofTK P fN fB L s o : ℝ) =
      ((∑ s ∈ (pats 2 P.K).filter (fun s => IsStTK P fN fB L s o),
        wtN P s * HofTK P fN fB L s o : ℕ) : ℝ) / (P.Q : ℝ) ^ P.K := by
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    have hlen : s.length = P.K := (Finset.mem_filter.mp hs).2.2.1
    have hcK : (s.filter (fun x => x.2)).length ≤ P.K := hlen ▸ List.length_filter_le _ _
    rw [wtW_eq, hlen]
    unfold wtN
    push_cast
    rw [div_pow, div_pow]
    have hQK : (P.Q : ℝ) ^ P.K =
        (P.Q : ℝ) ^ (P.K - (s.filter (fun x => x.2)).length) * (P.Q : ℝ) ^ (s.filter (fun x => x.2)).length := by
      rw [← pow_add, Nat.sub_add_cancel hcK]
    rw [hQK]
    field_simp
  have hst_r : ((P.wE : ℝ) + P.wC) * (((sumL (eN.map (nearContribT P))).getD i0 0 +
      (sumL (eB.map (bulkContribT P))).getD i0 0 : ℕ) : ℝ) * P.K0d ≤
      P.K0n * P.Hmin * (P.Q : ℝ) ^ (P.K + 1) := by exact_mod_cast hst
  have hnat_r : ((∑ s ∈ (pats 2 P.K).filter (fun s => IsStTK P fN fB L s o),
      wtN P s * HofTK P fN fB L s o : ℕ) : ℝ) ≤
      (((sumL (eN.map (nearContribT P))).getD i0 0 + (sumL (eB.map (bulkContribT P))).getD i0 0 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  generalize ((sumL (eN.map (nearContribT P))).getD i0 0 + (sumL (eB.map (bulkContribT P))).getD i0 0 : ℕ) = S
    at hst_r hnat_r
  rw [hreal]
  calc ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) *
        (((∑ s ∈ (pats 2 P.K).filter (fun s => IsStTK P fN fB L s o),
          wtN P s * HofTK P fN fB L s o : ℕ) : ℝ) / (P.Q : ℝ) ^ P.K)
      ≤ ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) * ((S : ℝ) / (P.Q : ℝ) ^ P.K) := by
        gcongr
    _ = ((P.wE : ℝ) + P.wC) * (S : ℝ) / (P.Q : ℝ) ^ (P.K + 1) := by
        field_simp
        ring
    _ ≤ ((P.K0n : ℝ) / P.K0d) * P.Hmin := by
        rw [div_le_iff₀ (by positivity), show (P.K0n : ℝ) / P.K0d * P.Hmin * (P.Q : ℝ) ^ (P.K + 1) =
          (P.K0n * P.Hmin * (P.Q : ℝ) ^ (P.K + 1)) / P.K0d by ring, le_div_iff₀ hKr]
        exact hst_r

end CertK

end QEC
