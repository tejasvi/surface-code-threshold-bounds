import QEC.Count.CertSoundA
import QEC.Count.CertSoundK
import QECCountComp.KernA

/-!
# Soundness of the kernel checks of an augmented certificate (rotated code, heights)

The kernel checks of `QECCountComp/KernA.lean` reach the listed states through two lookups `fN fB` (near states by
`ckeyA K σ h`, bulk states by `ckeyA K σ 0`), each returning (potential, mask), with the lists of entries `eN eB`: every
entry a lookup returns is in its list (`memN`, `memB`; for a tree store `fN = tN.find`, `eN = tN.toList`). The checks
(`CertOKAK`): the row of every entry, start completeness from every first-vertex height `h0 ≤ HC + K` and from `bigH`,
and the start bounds from the totals over the entries.

`IsStAK`, `HofAK` are `IsStA`, `HofA` with `potAK` in place of `potA`; we get the same hypotheses of `sum_legal_leT`
for `nxt = nxtA` and `Ex = ExA P.hN` as in `CertSoundA.lean`: `certAK_pos`, `certAK_closed`, `certAK_rows`,
`certAK_start`, `certAK_startSum`. A mask only marks candidates whose claimed exclusion is checked again
(`exclWinAK`), so the computed row of a state bounds the sum over its legal successors. The facts about heights, keys
and the translation lemma are those of `CertSoundA.lean`.
-/

namespace QEC

open Finset QECComp SeamShift CertSound CertSoundA

section Defs

variable (P : ParamsA) (fN fB : ℕ → Option (ℕ × ℕ)) (eN eB : List (ℕ × ℕ × ℕ))

/-- The states of the augmented certificate (kernel form). -/
def IsStAK (s : List (ℕ × Bool)) (h0 : ℤ) : Prop :=
  s.length = P.K ∧ DirOK 2 s ∧ (potAK P fN fB s (headHA s h0)).isSome

/-- The potential of a state of the augmented certificate (kernel form). -/
def HofAK (s : List (ℕ × Bool)) (h0 : ℤ) : ℕ := ((potAK P fN fB s (headHA s h0)).map Prod.fst).getD 0

/-- The checks of an augmented certificate in kernel form. -/
structure CertOKAK : Prop where
  memN : ∀ k h m, fN k = some (h, m) → (k, h, m) ∈ eN
  memB : ∀ k h m, fB k = some (h, m) → (k, h, m) ∈ eB
  hK : 2 ≤ P.K
  hHC : 2 * P.K + 2 ≤ P.HC
  hHC2 : P.HC ≤ 255
  hN0 : P.hN = 0
  hQ : 0 < P.Q
  hlamD : 0 < P.lamD
  hK0d : 0 < P.K0d
  near : ∀ e ∈ eN, nearRowAK P fN fB e = true
  bulk : ∀ e ∈ eB, bulkRowAK P fN fB e = true
  dfs : ∀ i, i ≤ P.HC + P.K + 1 → dfsAK P fN fB (offA P i) P.K [] = true
  start : startOKAK P (sumL (eN.map (nearContribA P))) (sumL (eB.map (bulkContribA P))) = true

end Defs

namespace CertSoundAK

/-! ## The computational checks, unfolded -/

section Computed

variable (P : ParamsA) (fN fB : ℕ → Option (ℕ × ℕ))

theorem exclWinAK_sound {h0 : ℤ} {u : List (ℕ × Bool)} (h : exclWinAK P h0 u = true) : ExclA P.hN h0 u := by
  unfold exclWinAK at h
  split at h
  · exact ⟨_, h⟩
  · exact absurd h (by simp)

theorem exclEndingAK_sound {h0 : ℤ} {u : List (ℕ × Bool)} (h : exclEndingAK P h0 u = true) :
    ∃ m, 2 ≤ m ∧ m ≤ u.length ∧ m ≤ P.K + 1 ∧
      ExclA P.hN (h0 - vdisp (u.take (u.length - m))) (u.drop (u.length - m)) := by
  unfold exclEndingAK at h
  rw [List.any_eq_true] at h
  obtain ⟨m, hm, hx⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [List.mem_range] at hm
  exact ⟨m, hx.1.1, hx.1.2, by omega, exclWinAK_sound P hx.2⟩

/-- The contribution of the candidate `xi` (step, index) to the computed row of `s` at head height `h` with mask
`mask`. -/
def rcontribAK (mask : ℕ) (s : List (ℕ × Bool)) (h : ℤ) (xi : (ℕ × Bool) × ℕ) : ℕ :=
  if (!selfAvoid 2 (s ++ [xi.1]) || decide (h - dl2 xi.1.1 < 0)) = true then 0
  else match potAK P fN fB (s ++ [xi.1]).tail (h - dl2 xi.1.1) with
    | some hm => if (mask / 2 ^ xi.2 % 2 == 1) = true then 0 else (if xi.1.2 then P.wC else P.wE) * hm.1
    | none => 0

/-- A candidate that is not skipped: a claimed exclusion is checked, and an unlisted target has an excluded
window. -/
def rgoodAK (mask : ℕ) (s : List (ℕ × Bool)) (h : ℤ) (xi : (ℕ × Bool) × ℕ) : Prop :=
  (!selfAvoid 2 (s ++ [xi.1]) || decide (h - dl2 xi.1.1 < 0)) = false →
    match potAK P fN fB (s ++ [xi.1]).tail (h - dl2 xi.1.1) with
    | some _ => (mask / 2 ^ xi.2 % 2 == 1) = true → exclWinAK P (h + vdisp s) (s ++ [xi.1]) = true
    | none => exclEndingAK P (h + vdisp s) (s ++ [xi.1]) = true

theorem rowSumAK_spec {mask : ℕ} {s : List (ℕ × Bool)} {h : ℤ} {tot : ℕ}
    (hr : rowSumAK P fN fB mask s h = some tot) :
    tot = (((candList 2).zip (List.range 8)).map (rcontribAK P fN fB mask s h)).sum ∧
      ∀ xi ∈ (candList 2).zip (List.range 8), rgoodAK P fN fB mask s h xi := by
  unfold rowSumAK at hr
  have := foldl_opt _ (rcontribAK P fN fB mask s h) (rgoodAK P fN fB mask s h) (fun x => rfl) ?_ ?_ _ 0 tot hr
  · simpa using this
  · intro a xi hx
    simp only [rgoodAK] at hx
    simp only [rcontribAK]
    cases h1 : (!selfAvoid 2 (s ++ [xi.1]) || decide (h - dl2 xi.1.1 < 0))
    · have hx1 := hx h1
      simp only [Bool.false_eq_true, ite_false]
      cases h2 : potAK P fN fB (s ++ [xi.1]).tail (h - dl2 xi.1.1) with
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
    · simp
  · intro a xi hx
    simp only [rgoodAK, not_imp] at hx
    obtain ⟨h1, hx'⟩ := hx
    simp only [h1, Bool.false_eq_true, ite_false]
    cases h2 : potAK P fN fB (s ++ [xi.1]).tail (h - dl2 xi.1.1) with
    | some hm =>
      rw [h2] at hx'
      simp only [not_imp, Bool.not_eq_true] at hx'
      simp [hx'.1, hx'.2]
    | none =>
      rw [h2] at hx'
      simp only [Bool.not_eq_true] at hx'
      simp [hx']

theorem rowCheckAK_spec {mask : ℕ} {s : List (ℕ × Bool)} {h : ℤ} {H : ℕ}
    (hr : rowCheckAK P fN fB mask s h H = true) :
    0 < P.Hmin ∧ P.Hmin ≤ H ∧
      ∃ tot, rowSumAK P fN fB mask s h = some tot ∧ tot * P.lamD ≤ P.lamN * P.Q * H := by
  unfold rowCheckAK at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  refine ⟨h1, h2, ?_⟩
  split at h3
  · rename_i tot htot
    exact ⟨tot, htot, by simpa using h3⟩
  · exact absurd h3 (by simp)

theorem potAK_neg {s : List (ℕ × Bool)} {h : ℤ} (hh : h < 0) : potAK P fN fB s h = none := by
  unfold potAK
  simp only [hh, ↓reduceIte]

theorem potAK_near {s : List (ℕ × Bool)} {h : ℤ} (h1 : 0 ≤ h) (h2 : h < P.HC) :
    potAK P fN fB s h = fN (ckeyA P.K s h.toNat) := by
  unfold potAK
  simp only [show ¬ (h < 0) by omega, h2, ↓reduceIte]

theorem potAK_far {s : List (ℕ × Bool)} {h : ℤ} (h2 : (P.HC : ℤ) ≤ h) :
    potAK P fN fB s h = fB (ckeyA P.K s 0) := by
  unfold potAK
  simp only [show ¬ (h < 0) by omega, show ¬ (h < (P.HC : ℤ)) by omega, ↓reduceIte]

end Computed

theorem mem_zip8 {x : ℕ × Bool} (hx : x ∈ candList 2) :
    (x, (candList 2).idxOf x) ∈ (candList 2).zip (List.range 8) :=
  CertSoundK.mem_zip_idx hx

theorem zip8_nodup : ((candList 2).zip (List.range 8)).Nodup := CertSoundK.zip_nodup 2

/-! ## Heights of states -/

variable {P : ParamsA} {fN fB : ℕ → Option (ℕ × ℕ)} {eN eB : List (ℕ × ℕ × ℕ)}

theorem K_le (hc : CertOKAK P fN fB eN eB) : P.K ≤ 126 := by
  have := hc.hHC
  have := hc.hHC2
  omega

/-- The computed row of a listed state (with the mask of its entry), and its potential. -/
theorem row_of_isStAK (hc : CertOKAK P fN fB eN eB) {s : List (ℕ × Bool)} {h0 : ℤ}
    (hs : IsStAK P fN fB s h0) :
    P.Hmin ≤ HofAK P fN fB s h0 ∧ ∃ mask tot, rowSumAK P fN fB mask s (hcOf P (headHA s h0)) = some tot ∧
      tot * P.lamD ≤ P.lamN * P.Q * HofAK P fN fB s h0 := by
  obtain ⟨hlen, hdir, hpot⟩ := hs
  unfold HofAK
  generalize headHA s h0 = h at hpot ⊢
  have hHC2 := hc.hHC2
  by_cases hneg : h < 0
  · rw [potAK_neg P fN fB hneg] at hpot
    exact absurd hpot (by simp)
  by_cases hn : h < P.HC
  · rw [potAK_near P fN fB (by omega) hn] at hpot ⊢
    obtain ⟨⟨H, m⟩, hf⟩ := Option.isSome_iff_exists.mp hpot
    have hrow := hc.near _ (hc.memN _ _ _ hf)
    simp only [nearRowAK, Bool.and_eq_true, decide_eq_true_eq] at hrow
    obtain ⟨-, hrow⟩ := hrow
    rw [decodeA_ckeyA hlen hdir, heightOf_ckeyA hlen, Int.toNat_of_nonneg (by omega)] at hrow
    have hoc : hcOf P h = h := by unfold hcOf; simp only [show h ≤ (P.HC : ℤ) by omega, ↓reduceIte]
    rw [hoc, hf]
    simp only [Option.map_some, Option.getD_some]
    obtain ⟨-, h2, tot, h3, h4⟩ := rowCheckAK_spec P fN fB hrow
    exact ⟨h2, m, tot, h3, h4⟩
  · rw [potAK_far P fN fB (by omega)] at hpot ⊢
    obtain ⟨⟨H, m⟩, hf⟩ := Option.isSome_iff_exists.mp hpot
    have hrow := hc.bulk _ (hc.memB _ _ _ hf)
    simp only [bulkRowAK, Bool.and_eq_true] at hrow
    obtain ⟨hr2, hr1⟩ := hrow
    rw [decodeA_ckeyA hlen hdir] at hr1 hr2
    rw [hf]
    simp only [Option.map_some, Option.getD_some]
    unfold hcOf
    by_cases hsm : h ≤ P.HC
    · simp only [hsm, ↓reduceIte]
      rw [show h = (P.HC : ℤ) by omega]
      obtain ⟨-, h2, tot, h3, h4⟩ := rowCheckAK_spec P fN fB hr1
      exact ⟨h2, _, tot, h3, h4⟩
    · simp only [hsm, ↓reduceIte]
      obtain ⟨-, h2, tot, h3, h4⟩ := rowCheckAK_spec P fN fB hr2
      exact ⟨h2, _, tot, h3, h4⟩

/-- The exclusions of the windows of a successor agree at the heights of the computed row and at the true heights. -/
theorem win_equivAK (hc : CertOKAK P fN fB eN eB) {s : List (ℕ × Bool)} {h0 : ℤ} (hlen : s.length = P.K)
    (x : ℕ × Bool) {j : ℕ} (hj : j < P.K) :
    ExclA P.hN (hcOf P (headHA s h0) + vdisp s - vdisp ((s ++ [x]).take j)) ((s ++ [x]).drop j) ↔
      ExclA P.hN (offAt nxtA h0 (s ++ [x]) j) ((s ++ [x]).drop j) := by
  rw [offAt_nxtA]
  unfold hcOf
  by_cases hsm : headHA s h0 ≤ P.HC
  · simp only [hsm, ↓reduceIte]
    unfold headHA
    ring_nf
  · simp only [hsm, ↓reduceIte]
    rw [hc.hN0]
    have hHC := hc.hHC
    have hK2 := K_le hc
    have hulen : (s ++ [x]).length = P.K + 1 := by simp [hlen]
    have hwl : (((s ++ [x]).drop j).length : ℤ) = P.K + 1 - j := by
      rw [List.length_drop, hulen]
      push_cast [show j ≤ P.K + 1 by omega]
      ring
    have htj : (s ++ [x]).take j = s.take j := List.take_append_of_le_length (by omega)
    have hsK : s.take P.K = s := by rw [← hlen]; exact List.take_length
    have hsub := vdisp_take_sub s (show j ≤ P.K by omega)
    rw [hsK] at hsub
    have hxj := vdisp_take_bounds s j
    have hxs := vdisp_bounds s
    rw [hlen] at hxs
    unfold headHA at hsm
    rw [htj]
    apply exclA_shift
    · rw [hwl]
      unfold bigH
      omega
    · rw [hwl]
      push_cast [Nat.cast_sub (show j ≤ P.K by omega)] at hsub
      omega

/-- The potential of a successor at the height of the computed row is its true potential. -/
theorem pot_succAK (hc : CertOKAK P fN fB eN eB) {s : List (ℕ × Bool)} {h0 : ℤ} (hlen : s.length = P.K)
    (x : ℕ × Bool) :
    potAK P fN fB (s ++ [x]).tail (hcOf P (headHA s h0) - dl2 x.1) =
      potAK P fN fB (s ++ [x]).tail (headHA (s ++ [x]).tail (offAt nxtA h0 s 1)) := by
  have hK1 := hc.hK
  have hs0 : s ≠ [] := by rintro rfl; simp at hlen; omega
  rw [headHA_next hs0]
  have hd := dl2_bounds x.1
  have hHC2 := hc.hHC2
  unfold hcOf
  by_cases hsm : headHA s h0 ≤ P.HC
  · simp only [hsm, ↓reduceIte]
  · simp only [hsm, ↓reduceIte]
    rw [potAK_far P fN fB (by unfold bigH; omega), potAK_far P fN fB (by omega)]

end CertSoundAK

open CertSoundAK CertSoundK

variable {P : ParamsA} {fN fB : ℕ → Option (ℕ × ℕ)} {eN eB : List (ℕ × ℕ × ℕ)}

/-! ## Positivity, closure and rows -/

theorem certAK_pos (hc : CertOKAK P fN fB eN eB) {s : List (ℕ × Bool)} {h0 : ℤ}
    (hs : IsStAK P fN fB s h0) : P.Hmin ≤ HofAK P fN fB s h0 :=
  (row_of_isStAK hc hs).1

theorem certAK_closed (hc : CertOKAK P fN fB eN eB) {s : List (ℕ × Bool)} {h0 : ℤ}
    (hs : IsStAK P fN fB s h0) {x : ℕ × Bool} (hx : SuccG nxtA (ExA P.hN) s h0 x) :
    IsStAK P fN fB (s ++ [x]).tail (offAt nxtA h0 s 1) := by
  have hs' := hs
  obtain ⟨hlen, hdir, -⟩ := hs
  have hK1 := hc.hK
  obtain ⟨-, mask, tot, htot, -⟩ := row_of_isStAK hc hs'
  obtain ⟨-, hgood⟩ := rowSumAK_spec P fN fB htot
  have hx1 : x.1 < 2 * 2 := hx.1
  have hg := hgood _ (mem_zip8 (mem_candList.mpr hx1))
  have hsa : selfAvoid 2 (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
  have hnn := succ_head_nonneg (by omega) hx
  have hnn' : ¬ (hcOf P (headHA s h0) - dl2 x.1 < 0) := by
    have hd := dl2_bounds x.1
    unfold hcOf
    split_ifs
    · omega
    · unfold bigH; omega
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro y hy
    rcases List.mem_append.mp (List.mem_of_mem_tail hy) with hy | hy
    · exact hdir y hy
    · rw [List.mem_singleton.mp hy]
      exact hx1
  · rw [← pot_succAK hc hlen x]
    cases hp : potAK P fN fB (s ++ [x]).tail (hcOf P (headHA s h0) - dl2 x.1) with
    | some _ => rfl
    | none =>
      exfalso
      have hcond : (!selfAvoid 2 (s ++ [x]) || decide (hcOf P (headHA s h0) - dl2 x.1 < 0)) = false := by
        simp [hsa, hnn']
      have hg' := hg hcond
      simp only [hp] at hg'
      obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingAK_sound P hg'
      have hulen : (s ++ [x]).length = s.length + 1 := by simp
      rw [hulen] at hmle hex
      have hj : s.length + 1 - m < P.K := by omega
      rw [win_equivAK hc hlen x hj] at hex
      exact hx.2.2 m hm2 hmle (Or.inl hex)

open scoped Classical in
theorem certAK_rows (hc : CertOKAK P fN fB eN eB) {s : List (ℕ × Bool)} {h0 : ℤ}
    (hs : IsStAK P fN fB s h0) :
    ∑ x ∈ (cands 2).filter (SuccG nxtA (ExA P.hN) s h0),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
        (HofAK P fN fB (s ++ [x]).tail (offAt nxtA h0 s 1) : ℝ) ≤
      ((P.lamN : ℝ) / P.lamD) * HofAK P fN fB s h0 := by
  have hs' := hs
  obtain ⟨hlen, hdir, -⟩ := hs
  have hK1 := hc.hK
  obtain ⟨-, mask, tot, htot, hrow⟩ := row_of_isStAK hc hs'
  obtain ⟨htot_eq, hgood⟩ := rowSumAK_spec P fN fB htot
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hc.hQ
  have hlamDr : (0 : ℝ) < P.lamD := by exact_mod_cast hc.hlamD
  set hh := hcOf P (headHA s h0) with hhh
  set Z := (candList 2).zip (List.range 8) with hZ
  let f : ℕ × Bool → (ℕ × Bool) × ℕ := fun x => (x, (candList 2).idxOf x)
  have hterm : ∀ x ∈ (cands 2).filter (SuccG nxtA (ExA P.hN) s h0),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
        (HofAK P fN fB (s ++ [x]).tail (offAt nxtA h0 s 1) : ℝ) =
      (rcontribAK P fN fB mask s hh (f x) : ℝ) / P.Q := by
    intro x hxm
    have hx := (Finset.mem_filter.mp hxm).2
    have hsa : selfAvoid 2 (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
    have hnn := succ_head_nonneg (by omega) hx
    have hnn' : ¬ (hh - dl2 x.1 < 0) := by
      have hd := dl2_bounds x.1
      rw [hhh]
      unfold hcOf
      split_ifs
      · omega
      · unfold bigH; omega
    have hcond : (!selfAvoid 2 (s ++ [x]) || decide (hh - dl2 x.1 < 0)) = false := by
      simp [hsa, hnn']
    obtain ⟨-, -, hp⟩ := certAK_closed hc hs' hx
    obtain ⟨⟨h', m'⟩, hh'⟩ := Option.isSome_iff_exists.mp hp
    have hps := pot_succAK hc hlen x (h0 := h0)
    rw [← hhh] at hps
    have hg := hgood (f x) (mem_zip8 (mem_candList.mpr hx.1)) hcond
    simp only [f] at hg
    rw [hps, hh'] at hg
    have hbit : (mask / 2 ^ (candList 2).idxOf x % 2 == 1) = false := by
      cases hb : (mask / 2 ^ (candList 2).idxOf x % 2 == 1)
      · rfl
      · exfalso
        have hE := exclWinAK_sound P (hg hb)
        have hw := win_equivAK hc hlen x (h0 := h0) (j := 0) (by omega)
        simp only [List.take_zero, vdisp_nil, sub_zero, List.drop_zero] at hw
        rw [← hhh] at hw
        rw [hw] at hE
        exact hx.2.2 (s.length + 1) (by omega) le_rfl (Or.inl (by simpa using hE))
    have hHof : HofAK P fN fB (s ++ [x]).tail (offAt nxtA h0 s 1) = h' := by
      unfold HofAK
      rw [hh']
      rfl
    rw [hHof]
    simp only [rcontribAK, f, hcond, Bool.false_eq_true, ite_false, hps, hh', hbit]
    unfold wtW
    obtain ⟨d, b⟩ := x
    cases b <;> simp [div_mul_eq_mul_div]
  have hinj : Set.InjOn f ↑((cands 2).filter (SuccG nxtA (ExA P.hN) s h0)) := by
    intro x _ y _ hxy
    exact (Prod.mk.inj hxy).1
  have himg : ((cands 2).filter (SuccG nxtA (ExA P.hN) s h0)).image f ⊆ Z.toFinset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [List.mem_toFinset]
    exact mem_zip8 (mem_candList.mpr (Finset.mem_filter.mp hx).2.1)
  have hsumZ : ∑ y ∈ Z.toFinset, (rcontribAK P fN fB mask s hh y : ℝ) = (tot : ℝ) := by
    rw [List.sum_toFinset _ zip8_nodup, htot_eq]
    push_cast
    rw [List.map_map]
    rfl
  calc ∑ x ∈ (cands 2).filter (SuccG nxtA (ExA P.hN) s h0),
        wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
          (HofAK P fN fB (s ++ [x]).tail (offAt nxtA h0 s 1) : ℝ)
      = ∑ x ∈ (cands 2).filter (SuccG nxtA (ExA P.hN) s h0), (rcontribAK P fN fB mask s hh (f x) : ℝ) / P.Q :=
        Finset.sum_congr rfl hterm
    _ = ∑ y ∈ ((cands 2).filter (SuccG nxtA (ExA P.hN) s h0)).image f, (rcontribAK P fN fB mask s hh y : ℝ) / P.Q :=
        (Finset.sum_image (f := fun y => (rcontribAK P fN fB mask s hh y : ℝ) / P.Q) hinj).symm
    _ ≤ ∑ y ∈ Z.toFinset, (rcontribAK P fN fB mask s hh y : ℝ) / P.Q :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
    _ = (tot : ℝ) / P.Q := by rw [← Finset.sum_div, hsumZ]
    _ ≤ ((P.lamN : ℝ) / P.lamD) * HofAK P fN fB s h0 := by
        rw [div_le_iff₀ hQr]
        have hrow' : (tot : ℝ) * P.lamD ≤ P.lamN * P.Q * (HofAK P fN fB s h0 : ℝ) := by exact_mod_cast hrow
        rw [show (P.lamN : ℝ) / P.lamD * (HofAK P fN fB s h0 : ℝ) * P.Q =
          (P.lamN * P.Q * (HofAK P fN fB s h0 : ℝ)) / P.lamD by ring, le_div_iff₀ hlamDr]
        exact hrow'

/-! ## Start completeness -/

namespace CertSoundAK

/-- Start completeness from the check `dfsAK` at `hd`, for a pattern whose vertices are at heights `≥ 0` from `hd` and
whose exclusions at the heights `hd - vdisp (s.take i)` imply its exclusions at its true heights. -/
theorem start_of_dfsAK {h0 hd : ℤ} {s : List (ℕ × Bool)} (hlen : s.length = P.K)
    (hdfs : dfsAK P fN fB hd P.K [] = true) (hleg : LegalG nxtA (ExA P.hN) (P.K + 1) h0 s)
    (hnn : ∀ i, 1 ≤ i → i ≤ P.K → 0 ≤ hd - vdisp (s.take i))
    (hwin : ∀ i m, 2 ≤ m → i + m ≤ P.K → ExclA P.hN (hd - vdisp (s.take i)) ((s.drop i).take m) →
      ExA P.hN (offAt nxtA h0 s i) ((s.drop i).take m)) :
    (potAK P fN fB s (hd - vdisp s)).isSome = true := by
  obtain ⟨hsa, hdir, hw⟩ := hleg
  have key : ∀ j, j ≤ P.K → dfsAK P fN fB hd (P.K - j) (s.take j) = true := by
    intro j
    induction j with
    | zero => intro _; simpa using hdfs
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      rw [show P.K - j = (P.K - (j + 1)) + 1 by omega] at h1
      simp only [dfsAK, List.all_eq_true] at h1
      have hjs : j < s.length := by omega
      have hx := h1 s[j] (mem_candList.mpr (hdir _ (List.getElem_mem hjs)))
      rw [List.take_append_getElem hjs] at hx
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hx
      have hlt : (s.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
      rcases hx with ((hx | hx) | hx) | hx
      · exfalso
        have := selfAvoid_iff.mpr (selfAv_take hsa (j + 1))
        rw [hx] at this
        exact absurd this (by simp)
      · exfalso
        have := hnn (j + 1) (by omega) hj
        omega
      · exact hx
      · exfalso
        obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingAK_sound P hx
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
  simpa only [dfsAK] using hK'

theorem offA_near {i : ℕ} (hi : i < P.HC + P.K + 1) : offA P i = (i : ℤ) := by
  unfold offA
  simp only [hi, ↓reduceIte]

theorem offA_big : offA P (P.HC + P.K + 1) = bigH := by
  unfold offA
  simp only [lt_irrefl, ↓reduceIte]

end CertSoundAK

theorem certAK_start (hc : CertOKAK P fN fB eN eB) {h0 : ℤ} (hh : 0 ≤ h0) {s : List (ℕ × Bool)}
    (hs : s.length = P.K) (hleg : LegalG nxtA (ExA P.hN) (P.K + 1) h0 s) : IsStAK P fN fB s h0 := by
  refine ⟨hs, hleg.2.1, ?_⟩
  have hK2 := hc.hK
  have hHC := hc.hHC
  have hKle := K_le hc
  have hHC2 := hc.hHC2
  have hverts : ∀ i, 1 ≤ i → i ≤ P.K → 0 ≤ h0 - vdisp (s.take i) := by
    intro i hi1 hi
    rw [← hs] at hleg hi
    exact legal_nonneg (by omega) hleg hi1 hi
  have hxs := vdisp_bounds s
  rw [hs] at hxs
  unfold headHA
  by_cases hn : h0 ≤ P.HC + P.K
  · -- a start near the top: the check `dfsAK` at `h0`
    have hd : dfsAK P fN fB h0 P.K [] = true := by
      have := hc.dfs h0.toNat (by omega)
      rwa [offA_near (by omega), Int.toNat_of_nonneg hh] at this
    exact start_of_dfsAK hs hd hleg hverts (fun i m _ _ hE => Or.inl (by rw [offAt_nxtA]; exact hE))
  · -- a start far from the top: the check `dfsAK` at `bigH`, by translation
    have hwin : ∀ i m, 2 ≤ m → i + m ≤ P.K → ExclA P.hN (bigH - vdisp (s.take i)) ((s.drop i).take m) →
        ExA P.hN (offAt nxtA h0 s i) ((s.drop i).take m) := by
      intro i m _ him hE
      left
      rw [offAt_nxtA]
      rw [hc.hN0] at hE ⊢
      have hwl : (((s.drop i).take m).length : ℤ) ≤ m := by exact_mod_cast List.length_take_le _ _
      have hxi := vdisp_take_bounds s i
      refine (exclA_shift ?_ ?_).mp hE
      · unfold bigH; omega
      · omega
    have hd : dfsAK P fN fB bigH P.K [] = true := by
      have := hc.dfs (P.HC + P.K + 1) le_rfl
      rwa [offA_big] at this
    have := start_of_dfsAK hs hd hleg (fun i _ hi => by
      have := vdisp_take_bounds s i; unfold bigH; omega) hwin
    rw [potAK_far P fN fB (by unfold bigH; omega)] at this
    rw [potAK_far P fN fB (by omega)]
    exact this

/-! ## The start sums -/

namespace CertSoundAK

theorem getD_addL : ∀ (a b : List ℕ) (t : ℕ), (addL a b).getD t 0 = a.getD t 0 + b.getD t 0
  | [], b, t => by simp [addL]
  | x :: xs, [], t => by simp [addL]
  | x :: xs, y :: ys, 0 => by simp [addL]
  | x :: xs, y :: ys, t + 1 => by
    have ih := getD_addL xs ys t
    simp only [addL, List.getD_cons_succ]
    exact ih

theorem getD_sumL (f : ℕ × ℕ × ℕ → List ℕ) (t : ℕ) : ∀ L : List (ℕ × ℕ × ℕ),
    (sumL (L.map f)).getD t 0 = (L.map (fun e => (f e).getD t 0)).sum
  | [] => by simp [sumL]
  | e :: L => by
    have ih := getD_sumL f t L
    simp only [List.map_cons, sumL, List.sum_cons]
    rw [getD_addL, ih]

/-- A sum over a finite set mapped injectively into a list is at most the sum over the list. -/
theorem sum_le_list_sum {β : Type*} [DecidableEq β] {S : Finset (List (ℕ × Bool))} (φ : List (ℕ × Bool) → β)
    (c : β → ℕ) (L : List β) (hinj : Set.InjOn φ S) (hmem : ∀ s ∈ S, φ s ∈ L) :
    ∑ s ∈ S, c (φ s) ≤ (L.map c).sum := by
  rw [← Finset.sum_image (f := c) hinj]
  calc ∑ e ∈ S.image φ, c e ≤ ∑ e ∈ L.toFinset, c e := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
          exact List.mem_toFinset.mpr (hmem s hs)
        · intro _ _ _
          exact Nat.zero_le _
    _ ≤ ∑ e ∈ L.toFinset, L.count e • c e := by
        apply Finset.sum_le_sum
        intro e he
        have : 1 ≤ L.count e := List.count_pos_iff.mpr (List.mem_toFinset.mp he)
        rw [smul_eq_mul]
        exact Nat.le_mul_of_pos_left _ this
    _ = (L.map c).sum := (Finset.sum_list_map_count L c).symm

theorem getD_map_range (n t : ℕ) (g : ℕ → ℕ) (ht : t < n) : ((List.range n).map g).getD t 0 = g t := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
  rfl

theorem wtA_eq (P : ParamsA) (σ : List (ℕ × Bool)) : wtA P σ = wtNA P σ := rfl

end CertSoundAK

open scoped Classical in
theorem certAK_startSum (hc : CertOKAK P fN fB eN eB) {h0 : ℤ} (hh : 0 ≤ h0) :
    ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) ^ 2 *
      ∑ s ∈ (pats 2 P.K).filter (fun s => IsStAK P fN fB s h0),
        wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) s * (HofAK P fN fB s h0 : ℝ) ≤
      ((P.K0n : ℝ) / P.K0d) * P.Hmin := by
  have hHC := hc.hHC
  have hHC2 := hc.hHC2
  have hKle := K_le hc
  set n := P.HC + P.K + 1 with hn
  -- the slot of the start
  let t : ℕ := if h0 ≤ P.HC + P.K then h0.toNat else n
  have ht : t < n + 1 := by
    simp only [t]
    split_ifs <;> omega
  set cN : ℕ × ℕ × ℕ → ℕ := fun e => (nearContribA P e).getD t 0 with hcN
  set cB : ℕ × ℕ × ℕ → ℕ := fun e => (bulkContribA P e).getD t 0 with hcB
  have hst : (P.wE + P.wC) ^ 2 * ((eN.map cN).sum + (eB.map cB).sum) * P.K0d ≤
      P.K0n * P.Hmin * P.Q ^ (P.K + 2) := by
    have h := hc.start
    unfold startOKAK at h
    rw [List.all_eq_true] at h
    have := h t (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at this
    rw [getD_sumL, getD_sumL] at this
    exact this
  -- (1) the bound in integers, state by state
  have hnat : ∑ s ∈ (pats 2 P.K).filter (fun s => IsStAK P fN fB s h0),
      wtNA P s * HofAK P fN fB s h0 ≤ (eN.map cN).sum + (eB.map cB).sum := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun s => headHA s h0 < P.HC)]
    apply add_le_add
    · -- near heads: the near entries
      let φ : List (ℕ × Bool) → ℕ × ℕ × ℕ := fun s =>
        match fN (ckeyA P.K s (headHA s h0).toNat) with
        | some hm => (ckeyA P.K s (headHA s h0).toNat, hm.1, hm.2)
        | none => (0, 0, 0)
      have hφ : ∀ s ∈ ((pats 2 P.K).filter (fun s => IsStAK P fN fB s h0)).filter (fun s => headHA s h0 < P.HC),
          ∃ H m, fN (ckeyA P.K s (headHA s h0).toNat) = some (H, m) ∧
            φ s = (ckeyA P.K s (headHA s h0).toNat, H, m) ∧ 0 ≤ headHA s h0 ∧ s.length = P.K ∧ DirOK 2 s ∧
            headHA s h0 < P.HC := by
        intro s hs
        simp only [Finset.mem_filter] at hs
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨hslen, hsdir, hsp⟩ := hsS
        have hs0 : 0 ≤ headHA s h0 := by
          by_contra hneg
          rw [potAK_neg P fN fB (by omega)] at hsp
          exact absurd hsp (by simp)
        rw [potAK_near P fN fB hs0 hsn] at hsp
        obtain ⟨⟨H, m⟩, hf⟩ := Option.isSome_iff_exists.mp hsp
        exact ⟨H, m, hf, by simp only [φ, hf], hs0, hslen, hsdir, hsn⟩
      have hle : ∀ s ∈ ((pats 2 P.K).filter (fun s => IsStAK P fN fB s h0)).filter (fun s => headHA s h0 < P.HC),
          wtNA P s * HofAK P fN fB s h0 = cN (φ s) := by
        intro s hs
        obtain ⟨H, m, hf, hφs, hs0, hslen, hsdir, hsn⟩ := hφ s hs
        rw [hφs]
        have hxs := vdisp_bounds s
        rw [hslen] at hxs
        have hnear : h0 ≤ P.HC + P.K := by unfold headHA at hsn; omega
        have htn : t = h0.toNat := by simp only [t, hnear, ↓reduceIte]
        have hHof : HofAK P fN fB s h0 = H := by
          unfold HofAK
          rw [potAK_near P fN fB hs0 hsn, hf]
          rfl
        rw [hHof]
        simp only [hcN, nearContribA]
        rw [getD_map_range _ _ _ (by omega)]
        simp only [decodeA_ckeyA hslen hsdir, heightOf_ckeyA hslen, Int.toNat_of_nonneg hs0]
        have hcond : (decide (t < P.HC + P.K + 1) && (headHA s h0 + vdisp s == (t : ℤ))) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          refine ⟨by omega, ?_⟩
          rw [htn, Int.toNat_of_nonneg hh]
          unfold headHA
          ring
        rw [if_pos hcond, wtA_eq]
      rw [Finset.sum_congr rfl hle]
      apply sum_le_list_sum φ cN eN
      · intro s hs u hu hsu
        obtain ⟨H, m, hf, hφs, -, hslen, hsdir, -⟩ := hφ s hs
        obtain ⟨H', m', hf', hφu, -, hulen, hudir, -⟩ := hφ u hu
        rw [hφs, hφu] at hsu
        have hk := (Prod.mk.inj hsu).1
        rw [← decodeA_ckeyA hslen hsdir (headHA s h0).toNat, hk, decodeA_ckeyA hulen hudir]
      · intro s hs
        obtain ⟨H, m, hf, hφs, -⟩ := hφ s hs
        rw [hφs]
        exact hc.memN _ _ _ hf
    · -- far heads: the bulk entries
      let φ : List (ℕ × Bool) → ℕ × ℕ × ℕ := fun s =>
        match fB (ckeyA P.K s 0) with
        | some hm => (ckeyA P.K s 0, hm.1, hm.2)
        | none => (0, 0, 0)
      have hφ : ∀ s ∈ ((pats 2 P.K).filter (fun s => IsStAK P fN fB s h0)).filter
          (fun s => ¬ headHA s h0 < P.HC),
          ∃ H m, fB (ckeyA P.K s 0) = some (H, m) ∧ φ s = (ckeyA P.K s 0, H, m) ∧ s.length = P.K ∧ DirOK 2 s ∧
            (P.HC : ℤ) ≤ headHA s h0 := by
        intro s hs
        simp only [Finset.mem_filter] at hs
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨hslen, hsdir, hsp⟩ := hsS
        rw [potAK_far P fN fB (by omega)] at hsp
        obtain ⟨⟨H, m⟩, hf⟩ := Option.isSome_iff_exists.mp hsp
        exact ⟨H, m, hf, by simp only [φ, hf], hslen, hsdir, by omega⟩
      have hle : ∀ s ∈ ((pats 2 P.K).filter (fun s => IsStAK P fN fB s h0)).filter
          (fun s => ¬ headHA s h0 < P.HC), wtNA P s * HofAK P fN fB s h0 = cB (φ s) := by
        intro s hs
        obtain ⟨H, m, hf, hφs, hslen, hsdir, hsn⟩ := hφ s hs
        rw [hφs]
        have hHof : HofAK P fN fB s h0 = H := by
          unfold HofAK
          rw [potAK_far P fN fB hsn, hf]
          rfl
        rw [hHof]
        simp only [hcB, bulkContribA]
        rw [getD_map_range _ _ _ (by omega)]
        simp only [decodeA_ckeyA hslen hsdir]
        unfold headHA at hsn
        by_cases hfar : h0 ≤ P.HC + P.K
        · have htn : t = h0.toNat := by simp only [t, hfar, ↓reduceIte]
          have h1 : ¬ (t = P.HC + P.K + 1) := by omega
          have h2 : ¬ ((t : ℤ) - vdisp s < (P.HC : ℤ)) := by
            rw [htn, Int.toNat_of_nonneg hh]
            omega
          simp only [beq_iff_eq, h1, ↓reduceIte, h2, wtA_eq]
        · have htn : t = P.HC + P.K + 1 := by simp only [t, hfar, ↓reduceIte, hn]
          simp only [beq_iff_eq, htn, ↓reduceIte, wtA_eq]
      rw [Finset.sum_congr rfl hle]
      apply sum_le_list_sum φ cB eB
      · intro s hs u hu hsu
        obtain ⟨H, m, hf, hφs, hslen, hsdir, -⟩ := hφ s hs
        obtain ⟨H', m', hf', hφu, hulen, hudir, -⟩ := hφ u hu
        rw [hφs, hφu] at hsu
        have hk := (Prod.mk.inj hsu).1
        rw [← decodeA_ckeyA hslen hsdir 0, hk, decodeA_ckeyA hulen hudir]
      · intro s hs
        obtain ⟨H, m, hf, hφs, -⟩ := hφ s hs
        rw [hφs]
        exact hc.memB _ _ _ hf
  -- (2) in reals
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hc.hQ
  have hKr : (0 : ℝ) < P.K0d := by exact_mod_cast hc.hK0d
  set T : ℕ := (eN.map cN).sum + (eB.map cB).sum with hT
  have hreal : ∑ s ∈ (pats 2 P.K).filter (fun s => IsStAK P fN fB s h0),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) s * (HofAK P fN fB s h0 : ℝ) =
      ((∑ s ∈ (pats 2 P.K).filter (fun s => IsStAK P fN fB s h0),
        wtNA P s * HofAK P fN fB s h0 : ℕ) : ℝ) / (P.Q : ℝ) ^ P.K := by
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    have hlen : s.length = P.K := (Finset.mem_filter.mp hs).2.1
    have hcK : nCA s ≤ P.K := by unfold nCA; rw [← hlen]; exact List.length_filter_le _ _
    rw [wtW_eq, hlen]
    unfold wtNA
    unfold nCA at hcK ⊢
    push_cast
    rw [div_pow, div_pow]
    have hQK : (P.Q : ℝ) ^ P.K =
        (P.Q : ℝ) ^ (P.K - (s.filter (fun x => x.2)).length) * (P.Q : ℝ) ^ (s.filter (fun x => x.2)).length := by
      rw [← pow_add, Nat.sub_add_cancel hcK]
    rw [hQK]
    field_simp
  have hst_r : ((P.wE : ℝ) + P.wC) ^ 2 * (T : ℝ) * P.K0d ≤
      P.K0n * P.Hmin * (P.Q : ℝ) ^ (P.K + 2) := by exact_mod_cast hst
  have hnat_r : ((∑ s ∈ (pats 2 P.K).filter (fun s => IsStAK P fN fB s h0),
      wtNA P s * HofAK P fN fB s h0 : ℕ) : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hnat
  rw [hreal]
  calc ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) ^ 2 *
        (((∑ s ∈ (pats 2 P.K).filter (fun s => IsStAK P fN fB s h0),
          wtNA P s * HofAK P fN fB s h0 : ℕ) : ℝ) / (P.Q : ℝ) ^ P.K)
      ≤ ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) ^ 2 * ((T : ℝ) / (P.Q : ℝ) ^ P.K) := by
        gcongr
    _ = ((P.wE : ℝ) + P.wC) ^ 2 * (T : ℝ) / (P.Q : ℝ) ^ (P.K + 2) := by
        field_simp
        ring
    _ ≤ ((P.K0n : ℝ) / P.K0d) * P.Hmin := by
        rw [div_le_iff₀ (by positivity), show (P.K0n : ℝ) / P.K0d * P.Hmin * (P.Q : ℝ) ^ (P.K + 2) =
          (P.K0n * P.Hmin * (P.Q : ℝ) ^ (P.K + 2)) / P.K0d by ring, le_div_iff₀ hKr]
        exact hst_r

end QEC
