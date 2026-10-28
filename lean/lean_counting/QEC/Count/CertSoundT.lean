import QEC.Count.SeamShift

/-!
# Soundness of the seam certificate checks on the torus

A state of the seam certificate on the torus of size `L` is a pattern `s` of `K` steps with a renormalized
first-vertex offset `o` (`IsStT`); its head offset is `headOffT L s o`. Its potential `HofT` is the near potential `G`
if the head offset is near (`-HC ≤ h < HC`), the bulk potential otherwise. From the checks (`CertOKT`) we get the
hypotheses of `sum_legal_leT` for `nxt = nxtT L` and `Ex = ExclT P.L0`, for every `L ≥ 4 (HC + K) + 4`:

* `certT_pos`, `certT_start`, `certT_closed`, `certT_rows`, `certT_startSum`.

The row of a state with head offset `h` is the computed row `rowSumT … s oc` at `oc = h` if `-HC - 1 ≤ h ≤ HC` (near
rows and the two interface rows; there is no wrap-around, so the computed offsets are the true ones) and at
`oc = bigO` otherwise (the windows are on one side of the seam both at their true offsets and at the offsets used by
the computed row, so the exclusions agree by the translation lemma `exclT_shift`).
-/

namespace QEC

open Finset QECComp SeamShift CertSound

section Cert

variable (P : ParamsT) (nk nG bk bH : Array ℕ)

/-- The head offset of a state (pattern `s`, first-vertex offset `o`) on the torus of size `L`. -/
def headOffT (L : ℕ) (s : List (ℕ × Bool)) (o : ℤ) : ℤ := offAt (nxtT L) o s s.length

/-- The states of the seam certificate on the torus of size `L`. -/
def IsStT (L : ℕ) (s : List (ℕ × Bool)) (o : ℤ) : Prop :=
  qoffZ L o = o ∧ s.length = P.K ∧ DirOK 2 s ∧ (potT P nk nG bk bH s (headOffT L s o)).isSome

/-- The potential of a state of the seam certificate. -/
def HofT (L : ℕ) (s : List (ℕ × Bool)) (o : ℤ) : ℕ := (potT P nk nG bk bH s (headOffT L s o)).getD 0

/-- The checks of a seam certificate. The last two fields are facts about the parameters that the soundness proof
needs: a positive start denominator, and near offsets that fit in the 12 bits of `nearKey`. -/
structure CertOKT : Prop where
  hK : 1 ≤ P.K
  hHC : P.HC = 2 * P.K + 2
  hQ : 0 < P.Q
  hlamD : 0 < P.lamD
  sizeG : nG.size = nk.size
  sizeH : bH.size = bk.size
  near : nearRowsOK P nk nG bk bH 0 nk.size = true
  bulk : bulkRowsOK P nk nG bk bH 0 bk.size = true
  dfsBig : dfsOffT P nk nG bk bH bigO = true
  dfsNear : rangeAllT (-((P.HC + P.K : ℕ) : ℤ)) (2 * (P.HC + P.K)) (dfsOffT P nk nG bk bH) = true
  startBig : startOKT P nk nG bk bH bigO = true
  startNear : rangeAllT (-((P.HC + P.K : ℕ) : ℤ)) (2 * (P.HC + P.K)) (startOKT P nk nG bk bH) = true
  hK0d : 0 < P.K0d
  hHC2 : P.HC ≤ 2048

namespace CertSoundT

/-! ## The computational checks, unfolded -/

theorem exclWinT_sound {o : ℤ} {u : List (ℕ × Bool)} (h : exclWinT P o u = true) : ExclT P.L0 o u := by
  unfold exclWinT at h
  split at h
  · exact ⟨_, h⟩
  · exact absurd h (by simp)

theorem exclEndingT_sound {o : ℤ} {u : List (ℕ × Bool)} (h : exclEndingT P o u = true) :
    ∃ m, 2 ≤ m ∧ m ≤ u.length ∧ m ≤ P.K + 1 ∧
      ExclT P.L0 (o + xdisp (u.take (u.length - m))) (u.drop (u.length - m)) := by
  unfold exclEndingT at h
  rw [List.any_eq_true] at h
  obtain ⟨m, hm, hx⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [List.mem_range] at hm
  exact ⟨m, hx.1.1, hx.1.2, by omega, exclWinT_sound P hx.2⟩

/-- The contribution of the candidate `x` to the computed row of `s` at head offset `o`. -/
def rcontribT (s : List (ℕ × Bool)) (o : ℤ) (x : ℕ × Bool) : ℕ :=
  if selfAvoid 2 (s ++ [x]) = true then
    match potT P nk nG bk bH (s ++ [x]).tail (o + xdisp [x]) with
    | some h => if exclWinT P (o - xdisp s) (s ++ [x]) = true then 0 else (if x.2 then P.wC else P.wE) * h
    | none => 0
  else 0

/-- A self-avoiding candidate that leads to an unlisted state has an excluded window. -/
def rgoodT (s : List (ℕ × Bool)) (o : ℤ) (x : ℕ × Bool) : Prop :=
  selfAvoid 2 (s ++ [x]) = true → potT P nk nG bk bH (s ++ [x]).tail (o + xdisp [x]) = none →
    exclEndingT P (o - xdisp s) (s ++ [x]) = true

theorem rowSumT_spec {s : List (ℕ × Bool)} {o : ℤ} {tot : ℕ} (h : rowSumT P nk nG bk bH s o = some tot) :
    tot = ((candList 2).map (rcontribT P nk nG bk bH s o)).sum ∧
      ∀ x ∈ candList 2, rgoodT P nk nG bk bH s o x := by
  unfold rowSumT at h
  have := foldl_opt _ (rcontribT P nk nG bk bH s o) (rgoodT P nk nG bk bH s o) (fun x => rfl) ?_ ?_
    (candList 2) 0 tot h
  · simpa using this
  · intro a x hx
    simp only [rgoodT] at hx
    simp only [rcontribT]
    by_cases h1 : selfAvoid 2 (s ++ [x]) = true
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      cases h2 : potT P nk nG bk bH (s ++ [x]).tail (o + xdisp [x]) with
      | some j =>
        simp only
        by_cases h3 : exclWinT P (o - xdisp s) (s ++ [x]) = true
        · simp [h3]
        · simp [h3]
      | none =>
        have h3 := hx h1 h2
        simp [h3]
    · simp only [Bool.not_eq_true] at h1
      simp [h1]
  · intro a x hx
    simp only [rgoodT, not_imp] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    simp only [Bool.not_eq_true] at h3
    simp [h1, h2, h3]

theorem rowOKT_spec {s : List (ℕ × Bool)} {o : ℤ} {hv : ℕ} (h : rowOKT P nk nG bk bH s o hv = true) :
    0 < P.Hmin ∧ P.Hmin ≤ hv ∧ ∃ tot, rowSumT P nk nG bk bH s o = some tot ∧ tot * P.lamD ≤ P.lamN * P.Q * hv := by
  unfold rowOKT at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · rename_i tot htot
    exact ⟨tot, htot, by simpa using h3⟩
  · exact absurd h3 (by simp)

theorem nearRow {hi : ℕ} (h : nearRowsOK P nk nG bk bH 0 hi = true) {i : ℕ} (hi' : i < hi) :
    rowOKT P nk nG bk bH (decodeKey 2 P.K (nk[i]! / 4096)) (((nk[i]! % 4096 : ℕ) : ℤ) - 2048) nG[i]! = true := by
  unfold nearRowsOK at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'.mpr ⟨i, by omega, by simp⟩)

theorem bulkRow {hi : ℕ} (h : bulkRowsOK P nk nG bk bH 0 hi = true) {i : ℕ} (hi' : i < hi) :
    rowOKT P nk nG bk bH (decodeKey 2 P.K bk[i]!) bigO bH[i]! = true ∧
      rowOKT P nk nG bk bH (decodeKey 2 P.K bk[i]!) P.HC bH[i]! = true ∧
      rowOKT P nk nG bk bH (decodeKey 2 P.K bk[i]!) (-(P.HC : ℤ) - 1) bH[i]! = true := by
  unfold bulkRowsOK at h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range'.mpr ⟨i, by omega, by simp⟩)
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- Near keys decode to their pattern and head offset. -/
theorem nearKey_decode {K : ℕ} {s : List (ℕ × Bool)} (hs : s.length = K) (hd : DirOK 2 s) {h : ℤ}
    (h1 : -2048 ≤ h) (h2 : h < 2048) :
    decodeKey 2 K (nearKey s h / 4096) = s ∧ (((nearKey s h % 4096 : ℕ) : ℤ) - 2048) = h := by
  have ht : ((h + 2048).toNat : ℤ) = h + 2048 := Int.toNat_of_nonneg (by omega)
  have hlt : (h + 2048).toNat < 4096 := by omega
  unfold nearKey
  have e1 : (keyOf 2 s * 4096 + (h + 2048).toNat) / 4096 = keyOf 2 s := by omega
  have e2 : (keyOf 2 s * 4096 + (h + 2048).toNat) % 4096 = (h + 2048).toNat := by omega
  rw [e1, e2, decodeKey_keyOf (by norm_num) K s hs hd]
  exact ⟨rfl, by omega⟩

theorem potT_near {s : List (ℕ × Bool)} {h : ℤ} (h1 : -(P.HC : ℤ) ≤ h) (h2 : h < P.HC) :
    potT P nk nG bk bH s h = (lookup nk (nearKey s h)).map (fun j => nG[j]!) := by
  unfold potT
  rw [if_pos ⟨h1, h2⟩]

theorem potT_far {s : List (ℕ × Bool)} {h : ℤ} (hf : ¬ (-(P.HC : ℤ) ≤ h ∧ h < P.HC)) :
    potT P nk nG bk bH s h = (lookup bk (keyOf 2 s)).map (fun j => bH[j]!) := by
  unfold potT
  rw [if_neg hf]

/-! ## Offsets of states -/

variable {P nk nG bk bH}

/-- The head offset of the computed row of a state with head offset `h`. -/
def ocOf (P : ParamsT) (h : ℤ) : ℤ := if -(P.HC : ℤ) - 1 ≤ h ∧ h ≤ P.HC then h else bigO

theorem headOffT_eq {L : ℕ} {s : List (ℕ × Bool)} {o : ℤ} (ho : qoffZ L o = o) :
    headOffT L s o = qoffZ L (o + xdisp s) := by
  unfold headOffT
  rw [offAt_nxtT ho, List.take_length]

theorem renorm_bounds {L : ℕ} (hL : 0 < L) {o : ℤ} (ho : qoffZ L o = o) : -(L : ℤ) ≤ 2 * o ∧ 2 * o < L := by
  have := qoffZ_bounds hL o
  rwa [ho] at this

theorem K_le (hc : CertOKT P nk nG bk bH) : P.K ≤ 1023 := by
  have h1 := hc.hHC
  have h2 := hc.hHC2
  omega

/-- The head offset of the next state. -/
theorem headOffT_next {L : ℕ} {s : List (ℕ × Bool)} {o : ℤ} (ho : qoffZ L o = o) (hs : s ≠ []) (x : ℕ × Bool) :
    headOffT L (s ++ [x]).tail (offAt (nxtT L) o s 1) = qoffZ L (headOffT L s o + dxOf x.1) := by
  obtain ⟨a, s', rfl⟩ := List.exists_cons_of_ne_nil hs
  have ho' : qoffZ L (offAt (nxtT L) o (a :: s') 1) = offAt (nxtT L) o (a :: s') 1 := by
    rw [offAt_nxtT ho]
    exact qoffZ_idem _
  rw [headOffT_eq ho', offAt_nxtT ho, headOffT_eq ho, qoffZ_add, qoffZ_add]
  congr 1
  simp only [List.take_succ_cons, List.take_zero, List.cons_append, List.tail_cons, xdisp_append, xdisp_cons,
    xdisp_nil]
  ring

/-- With no wrap-around (`-HC - 1 ≤ h ≤ HC`), the head offset is the plain sum. -/
theorem head_exact {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L) {s : List (ℕ × Bool)}
    {o : ℤ} (ho : qoffZ L o = o) (hlen : s.length = P.K) (h1 : -(P.HC : ℤ) - 1 ≤ headOffT L s o)
    (h2 : headOffT L s o ≤ P.HC) : headOffT L s o = o + xdisp s := by
  have hL0 : 0 < L := by omega
  have hLz : (4 * ((P.HC : ℤ) + P.K) + 4 : ℤ) ≤ L := by exact_mod_cast hL
  have hb := renorm_bounds hL0 ho
  have hx := xdisp_bounds s
  rw [hlen] at hx
  rw [headOffT_eq ho] at h1 h2 ⊢
  rcases qoffZ_cases hL0 (b := o + xdisp s) (by omega) (by omega) with ⟨-, -, c⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩
  · exact c
  · rw [c2] at h1; omega
  · rw [c2] at h2; omega

/-! ## The three facts behind the rows -/

/-- The computed row of a listed state, and its potential. -/
theorem row_of_isStT (hc : CertOKT P nk nG bk bH) {L : ℕ} {s : List (ℕ × Bool)} {o : ℤ}
    (hs : IsStT P nk nG bk bH L s o) :
    P.Hmin ≤ HofT P nk nG bk bH L s o ∧ ∃ tot, rowSumT P nk nG bk bH s (ocOf P (headOffT L s o)) = some tot ∧
      tot * P.lamD ≤ P.lamN * P.Q * HofT P nk nG bk bH L s o := by
  obtain ⟨-, hlen, hdir, hpot⟩ := hs
  unfold HofT
  generalize headOffT L s o = h at hpot ⊢
  have hHC2 := hc.hHC2
  by_cases hn : -(P.HC : ℤ) ≤ h ∧ h < P.HC
  · rw [potT_near P nk nG bk bH hn.1 hn.2] at hpot ⊢
    rw [Option.isSome_map] at hpot
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hpot
    obtain ⟨hjlt, hk⟩ := lookup_some hj
    have hrow := nearRow P nk nG bk bH hc.near hjlt
    obtain ⟨hd1, hd2⟩ := nearKey_decode hlen hdir (h := h) (by omega) (by omega)
    rw [hk, hd1, hd2] at hrow
    have hoc : ocOf P h = h := by unfold ocOf; rw [if_pos ⟨by omega, by omega⟩]
    rw [hoc, hj]
    obtain ⟨-, h2, h3⟩ := rowOKT_spec P nk nG bk bH hrow
    exact ⟨h2, h3⟩
  · rw [potT_far P nk nG bk bH hn] at hpot ⊢
    rw [Option.isSome_map] at hpot
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hpot
    obtain ⟨hjlt, hk⟩ := lookup_some hj
    obtain ⟨hr1, hr2, hr3⟩ := bulkRow P nk nG bk bH hc.bulk hjlt
    rw [hk, decodeKey_keyOf (by norm_num) P.K s hlen hdir] at hr1 hr2 hr3
    rw [hj]
    simp only [Option.map_some, Option.getD_some]
    unfold ocOf
    by_cases hsm : -(P.HC : ℤ) - 1 ≤ h ∧ h ≤ P.HC
    · rw [if_pos hsm]
      rcases (show h = P.HC ∨ h = -(P.HC : ℤ) - 1 by omega) with rfl | rfl
      · obtain ⟨-, h2, h3⟩ := rowOKT_spec P nk nG bk bH hr2
        exact ⟨h2, h3⟩
      · obtain ⟨-, h2, h3⟩ := rowOKT_spec P nk nG bk bH hr3
        exact ⟨h2, h3⟩
    · rw [if_neg hsm]
      obtain ⟨-, h2, h3⟩ := rowOKT_spec P nk nG bk bH hr1
      exact ⟨h2, h3⟩

theorem xdisp_take_add (u : List (ℕ × Bool)) (j i : ℕ) :
    xdisp (u.take j) + xdisp ((u.drop j).take i) = xdisp (u.take (j + i)) := by
  rw [List.take_add, xdisp_append]

/-- The exclusions of the windows of a successor agree at the offsets of the computed row and at the true
offsets. -/
theorem win_equiv (hc : CertOKT P nk nG bk bH) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L) {s : List (ℕ × Bool)}
    {o : ℤ} (ho : qoffZ L o = o) (hlen : s.length = P.K) (x : ℕ × Bool) {j : ℕ} (hj : j < P.K) :
    ExclT P.L0 (ocOf P (headOffT L s o) - xdisp s + xdisp ((s ++ [x]).take j)) ((s ++ [x]).drop j) ↔
      ExclT P.L0 (offAt (nxtT L) o (s ++ [x]) j) ((s ++ [x]).drop j) := by
  have hL0 : 0 < L := by omega
  have hLz : (4 * ((P.HC : ℤ) + P.K) + 4 : ℤ) ≤ L := by exact_mod_cast hL
  have hHC : (P.HC : ℤ) = 2 * P.K + 2 := by exact_mod_cast hc.hHC
  have hK1 : (1 : ℤ) ≤ P.K := by exact_mod_cast hc.hK
  have hK2 : (P.K : ℤ) ≤ 1023 := by exact_mod_cast K_le hc
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
    · -- the true offsets: on one side, by the head offset (far from the seam)
      have hδ := xdisp_take_bounds ((s ++ [x]).drop j) (P.K - j)
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

/-- The potential of a successor at the offset of the computed row is its true potential. -/
theorem pot_succ (hc : CertOKT P nk nG bk bH) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L) {s : List (ℕ × Bool)}
    {o : ℤ} (ho : qoffZ L o = o) (hlen : s.length = P.K) (x : ℕ × Bool) :
    potT P nk nG bk bH (s ++ [x]).tail (ocOf P (headOffT L s o) + xdisp [x]) =
      potT P nk nG bk bH (s ++ [x]).tail (headOffT L (s ++ [x]).tail (offAt (nxtT L) o s 1)) := by
  have hL0 : 0 < L := by omega
  have hLz : (4 * ((P.HC : ℤ) + P.K) + 4 : ℤ) ≤ L := by exact_mod_cast hL
  have hK1 := hc.hK
  have hHC : (P.HC : ℤ) = 2 * P.K + 2 := by exact_mod_cast hc.hHC
  have hK2 : (P.K : ℤ) ≤ 1023 := by exact_mod_cast K_le hc
  have hs0 : s ≠ [] := by rintro rfl; simp at hlen; omega
  rw [headOffT_next ho hs0, xdisp_single]
  have hdx := dxOf_bounds x.1
  have hh := qoffZ_bounds hL0 (o + xdisp s)
  rw [← headOffT_eq ho] at hh
  unfold ocOf
  by_cases hsm : -(P.HC : ℤ) - 1 ≤ headOffT L s o ∧ headOffT L s o ≤ P.HC
  · rw [if_pos hsm, qoffZ_of_bounds hL0 (by omega) (by omega)]
  · rw [if_neg hsm, potT_far P nk nG bk bH (by unfold bigO; omega)]
    rcases qoffZ_cases hL0 (b := headOffT L s o + dxOf x.1) (by omega) (by omega) with ⟨-, -, c⟩ | ⟨c1, c2⟩ |
      ⟨c1, c2⟩
    · rw [potT_far P nk nG bk bH (by rw [c]; omega)]
    · rw [potT_far P nk nG bk bH (by rw [c2]; omega)]
    · rw [potT_far P nk nG bk bH (by rw [c2]; omega)]

end CertSoundT

open CertSoundT

variable {P nk nG bk bH}

/-! ## Positivity, closure and rows -/

theorem certT_pos (hc : CertOKT P nk nG bk bH) {L : ℕ} {s : List (ℕ × Bool)} {o : ℤ}
    (hs : IsStT P nk nG bk bH L s o) : P.Hmin ≤ HofT P nk nG bk bH L s o :=
  (row_of_isStT hc hs).1

theorem certT_closed (hc : CertOKT P nk nG bk bH) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L)
    {s : List (ℕ × Bool)} {o : ℤ} (hs : IsStT P nk nG bk bH L s o) {x : ℕ × Bool}
    (hx : SuccG (nxtT L) (ExclT P.L0) s o x) :
    IsStT P nk nG bk bH L (s ++ [x]).tail (offAt (nxtT L) o s 1) := by
  have hs' := hs
  obtain ⟨ho, hlen, hdir, -⟩ := hs
  obtain ⟨-, tot, htot, -⟩ := row_of_isStT hc hs'
  obtain ⟨-, hgood⟩ := rowSumT_spec P nk nG bk bH htot
  have hx1 : x.1 < 2 * 2 := hx.1
  have hg := hgood x (mem_candList.mpr hx1)
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
  · rw [← pot_succ hc hL ho hlen x]
    cases hp : potT P nk nG bk bH (s ++ [x]).tail (ocOf P (headOffT L s o) + xdisp [x]) with
    | some _ => rfl
    | none =>
      exfalso
      obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingT_sound P (hg hsa hp)
      have hulen : (s ++ [x]).length = s.length + 1 := by simp
      rw [hulen] at hmle hex
      have hj : s.length + 1 - m < P.K := by omega
      rw [win_equiv hc hL ho hlen x hj] at hex
      exact hx.2.2 m hm2 hmle hex

open scoped Classical in
theorem certT_rows (hc : CertOKT P nk nG bk bH) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L)
    {s : List (ℕ × Bool)} {o : ℤ} (hs : IsStT P nk nG bk bH L s o) :
    ∑ x ∈ (cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
        (HofT P nk nG bk bH L (s ++ [x]).tail (offAt (nxtT L) o s 1) : ℝ) ≤
      ((P.lamN : ℝ) / P.lamD) * HofT P nk nG bk bH L s o := by
  have hs' := hs
  obtain ⟨ho, hlen, hdir, -⟩ := hs
  have hK1 := hc.hK
  obtain ⟨-, tot, htot, hrow⟩ := row_of_isStT hc hs'
  obtain ⟨htot_eq, -⟩ := rowSumT_spec P nk nG bk bH htot
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hc.hQ
  have hlamDr : (0 : ℝ) < P.lamD := by exact_mod_cast hc.hlamD
  have hterm : ∀ x ∈ (cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
        (HofT P nk nG bk bH L (s ++ [x]).tail (offAt (nxtT L) o s 1) : ℝ) =
      (rcontribT P nk nG bk bH s (ocOf P (headOffT L s o)) x : ℝ) / P.Q := by
    intro x hxm
    have hx := (Finset.mem_filter.mp hxm).2
    have hsa : selfAvoid 2 (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
    have hnex : exclWinT P (ocOf P (headOffT L s o) - xdisp s) (s ++ [x]) = false := by
      cases he : exclWinT P (ocOf P (headOffT L s o) - xdisp s) (s ++ [x])
      · rfl
      · exfalso
        have hE := exclWinT_sound P he
        have hw := win_equiv hc hL ho hlen x hc.hK
        simp only [List.take_zero, xdisp_nil, add_zero, List.drop_zero] at hw
        rw [hw] at hE
        exact hx.2.2 (s.length + 1) (by omega) le_rfl (by simpa using hE)
    obtain ⟨-, -, -, hp⟩ := certT_closed hc hL hs' hx
    obtain ⟨h', hh'⟩ := Option.isSome_iff_exists.mp hp
    have hps := pot_succ hc hL ho hlen x
    have hHof : HofT P nk nG bk bH L (s ++ [x]).tail (offAt (nxtT L) o s 1) = h' := by
      unfold HofT
      rw [hh']
      rfl
    rw [hHof]
    simp only [rcontribT, hsa, ite_true, hps, hh', hnex, Bool.false_eq_true, ite_false]
    unfold wtW
    obtain ⟨d, b⟩ := x
    cases b <;> simp [div_mul_eq_mul_div]
  have hsumC : ∑ x ∈ cands 2, (rcontribT P nk nG bk bH s (ocOf P (headOffT L s o)) x : ℝ) = (tot : ℝ) := by
    rw [cands_eq_toFinset, List.sum_toFinset _ (candList_nodup _), htot_eq]
    push_cast
    rw [List.map_map]
    rfl
  calc ∑ x ∈ (cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o),
        wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
          (HofT P nk nG bk bH L (s ++ [x]).tail (offAt (nxtT L) o s 1) : ℝ)
      = ∑ x ∈ (cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o),
          (rcontribT P nk nG bk bH s (ocOf P (headOffT L s o)) x : ℝ) / P.Q := Finset.sum_congr rfl hterm
    _ ≤ ∑ x ∈ cands 2, (rcontribT P nk nG bk bH s (ocOf P (headOffT L s o)) x : ℝ) / P.Q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (tot : ℝ) / P.Q := by rw [← Finset.sum_div, hsumC]
    _ ≤ ((P.lamN : ℝ) / P.lamD) * HofT P nk nG bk bH L s o := by
        rw [div_le_iff₀ hQr]
        have hrow' : (tot : ℝ) * P.lamD ≤ P.lamN * P.Q * (HofT P nk nG bk bH L s o : ℝ) := by exact_mod_cast hrow
        rw [show (P.lamN : ℝ) / P.lamD * (HofT P nk nG bk bH L s o : ℝ) * P.Q =
          (P.lamN * P.Q * (HofT P nk nG bk bH L s o : ℝ)) / P.lamD by ring, le_div_iff₀ hlamDr]
        exact hrow'

/-! ## Start completeness -/

namespace CertSoundT

theorem rangeAllT_of {lo : ℤ} {cnt : ℕ} {f : ℤ → Bool} (h : rangeAllT lo cnt f = true) {q : ℤ} (h1 : lo ≤ q)
    (h2 : q < lo + cnt) : f q = true := by
  unfold rangeAllT at h
  rw [List.all_eq_true] at h
  have := h (q - lo).toNat (List.mem_range.mpr (by omega))
  rwa [show lo + ((q - lo).toNat : ℤ) = q by omega] at this

theorem exclEndingT_single (o : ℤ) (x : ℕ × Bool) : exclEndingT P o [x] = false := by
  unfold exclEndingT
  rw [List.any_eq_false]
  intro m _
  simp only [List.length_singleton, Bool.and_eq_true, decide_eq_true_eq, not_and]
  intro h1 h2
  omega

/-- Start completeness from the check `dfsOffT` at `o0`, for a pattern whose exclusions at the offsets
`o0 + xdisp (s.take i)` imply its exclusions at its true offsets. -/
theorem start_of_dfs {L : ℕ} {o o0 : ℤ} {s : List (ℕ × Bool)} (hK : 1 ≤ P.K) (hlen : s.length = P.K)
    (hdfs : dfsOffT P nk nG bk bH o0 = true) (hleg : LegalG (nxtT L) (ExclT P.L0) (P.K + 1) o s)
    (hwin : ∀ i m, 2 ≤ m → i + m ≤ P.K → ExclT P.L0 (o0 + xdisp (s.take i)) ((s.drop i).take m) →
      ExclT P.L0 (offAt (nxtT L) o s i) ((s.drop i).take m)) :
    (potT P nk nG bk bH s (o0 + xdisp s)).isSome = true := by
  obtain ⟨hsa, hdir, hw⟩ := hleg
  have key : ∀ j, 1 ≤ j → j ≤ P.K → dfsT P nk nG bk bH o0 (P.K - j) (s.take j) = true := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro _ hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · -- the first step: `dfsOffT`
        have hs0 : 0 < s.length := by omega
        have hmem : s[0] ∈ candList 2 := mem_candList.mpr (hdir _ (List.getElem_mem hs0))
        obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hmem
        unfold dfsOffT at hdfs
        rw [List.all_eq_true] at hdfs
        have hx := hdfs k (List.mem_range.mpr hk)
        simp only [dfsTopT, List.getElem?_eq_getElem hk, hke] at hx
        have h1 : s.take (0 + 1) = [s[0]] := by
          rw [Nat.zero_add, List.take_one, List.head?_eq_getElem? ]
          simp [List.getElem?_eq_getElem hs0]
        have hsa1 : selfAvoid 2 [s[0]] = true := by
          rw [← h1]
          exact selfAvoid_iff.mpr (selfAv_take hsa 1)
        rw [hsa1, exclEndingT_single] at hx
        simp only [Bool.not_true, Bool.false_or] at hx
        rw [h1, show P.K - (0 + 1) = P.K - 1 by omega]
        exact hx
      · have h1 := ih (by omega) (by omega)
        rw [show P.K - j = (P.K - (j + 1)) + 1 by omega] at h1
        simp only [dfsT, List.all_eq_true] at h1
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
          obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingT_sound P hx
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
        · exact hx
  have hK' := key P.K hK le_rfl
  rw [Nat.sub_self, List.take_of_length_le (by omega)] at hK'
  simpa only [dfsT] using hK'

end CertSoundT

theorem certT_start (hc : CertOKT P nk nG bk bH) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L) {o : ℤ}
    (ho : qoffZ L o = o) {s : List (ℕ × Bool)} (hs : s.length = P.K)
    (hleg : LegalG (nxtT L) (ExclT P.L0) (P.K + 1) o s) : IsStT P nk nG bk bH L s o := by
  refine ⟨ho, hs, hleg.2.1, ?_⟩
  have hL0 : 0 < L := by omega
  have hLz : (4 * ((P.HC : ℤ) + P.K) + 4 : ℤ) ≤ L := by exact_mod_cast hL
  have hHC : (P.HC : ℤ) = 2 * P.K + 2 := by exact_mod_cast hc.hHC
  have hK2 : (P.K : ℤ) ≤ 1023 := by exact_mod_cast K_le hc
  have hb := renorm_bounds hL0 ho
  have hxs := xdisp_bounds s
  rw [hs] at hxs
  by_cases hn : -((P.HC + P.K : ℕ) : ℤ) ≤ o ∧ o < ((P.HC + P.K : ℕ) : ℤ)
  · -- a start near the seam: the check `dfsOffT` at `o`, no wrap-around
    push_cast at hn
    have hd : dfsOffT P nk nG bk bH o = true :=
      rangeAllT_of hc.dfsNear (by push_cast; omega) (by push_cast; omega)
    have hwin : ∀ i m, 2 ≤ m → i + m ≤ P.K → ExclT P.L0 (o + xdisp (s.take i)) ((s.drop i).take m) →
        ExclT P.L0 (offAt (nxtT L) o s i) ((s.drop i).take m) := by
      intro i m _ him hE
      have hxi := xdisp_take_bounds s i
      rw [offAt_nxtT ho, qoffZ_of_bounds hL0 (by omega) (by omega)]
      exact hE
    have := start_of_dfs hc.hK hs hd hleg hwin
    rw [headOffT_eq ho, qoffZ_of_bounds hL0 (by omega) (by omega)]
    exact this
  · -- a start far from the seam: the check `dfsOffT` at `bigO`, by translation
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
    have := start_of_dfs hc.hK hs hc.dfsBig hleg hwin
    rw [potT_far P nk nG bk bH (by unfold bigO; omega)] at this
    rw [headOffT_eq ho]
    rcases qoffZ_cases hL0 (b := o + xdisp s) (by omega) (by omega) with ⟨-, -, c⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩
    · rw [c, potT_far P nk nG bk bH (by omega)]
      exact this
    · rw [c2, potT_far P nk nG bk bH (by omega)]
      exact this
    · rw [c2, potT_far P nk nG bk bH (by omega)]
      exact this

/-! ## The start sum -/

namespace CertSoundT

/-- A fold that adds `c i`. -/
theorem foldl_acc_add (F : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (hF : ∀ acc i, F acc i = acc + c i) :
    ∀ (l : List ℕ) (a : ℕ), l.foldl F a = a + (l.map c).sum
  | [], a => by simp
  | i :: l, a => by
    simp only [List.foldl, List.map_cons, List.sum_cons]
    rw [foldl_acc_add F c hF l, hF]
    ring

/-- The weight of a pattern scaled by `Q^K` (the weight of `startSumT`). -/
def wtN (P : ParamsT) (σ : List (ℕ × Bool)) : ℕ :=
  P.wE ^ (P.K - (σ.filter (fun x => x.2)).length) * P.wC ^ (σ.filter (fun x => x.2)).length

/-- The near terms of the start sum. -/
def cN (P : ParamsT) (nk nG : Array ℕ) (o0 : ℤ) (i : ℕ) : ℕ :=
  if (((nk[i]! % 4096 : ℕ) : ℤ) - 2048) - xdisp (decodeKey 2 P.K (nk[i]! / 4096)) = o0 then
    wtN P (decodeKey 2 P.K (nk[i]! / 4096)) * nG[i]! else 0

/-- The bulk terms of the start sum. -/
def cB (P : ParamsT) (bk bH : Array ℕ) (o0 : ℤ) (j : ℕ) : ℕ :=
  if -(P.HC : ℤ) ≤ o0 + xdisp (decodeKey 2 P.K bk[j]!) ∧ o0 + xdisp (decodeKey 2 P.K bk[j]!) < P.HC then 0
  else wtN P (decodeKey 2 P.K bk[j]!) * bH[j]!

theorem startSumT_eq (o0 : ℤ) : startSumT P nk nG bk bH o0 =
    ∑ i ∈ Finset.range nk.size, cN P nk nG o0 i + ∑ j ∈ Finset.range bk.size, cB P bk bH o0 j := by
  unfold startSumT
  dsimp only
  rw [foldl_acc_add _ (cN P nk nG o0) ?_, foldl_acc_add _ (cB P bk bH o0) ?_, list_sum_range, list_sum_range,
    Nat.zero_add, Nat.zero_add]
  · intro acc j
    unfold cB wtN
    split_ifs <;> simp
  · intro acc i
    unfold cN wtN
    by_cases h : (((nk[i]! % 4096 : ℕ) : ℤ) - 2048) - xdisp (decodeKey 2 P.K (nk[i]! / 4096)) = o0
    · have hb : ((((nk[i]! % 4096 : ℕ) : ℤ) - 2048) - xdisp (decodeKey 2 P.K (nk[i]! / 4096)) == o0) = true :=
        beq_iff_eq.mpr h
      rw [if_pos hb, if_pos h]
    · have hb : ¬ (((((nk[i]! % 4096 : ℕ) : ℤ) - 2048) - xdisp (decodeKey 2 P.K (nk[i]! / 4096)) == o0) = true) :=
        fun hc => h (beq_iff_eq.mp hc)
      rw [if_neg hb, if_neg h, Nat.add_zero]

/-- A start near the seam: the head offset is the plain sum. -/
theorem head_exact_start {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L) {s : List (ℕ × Bool)} {o : ℤ}
    (ho : qoffZ L o = o) (hlen : s.length = P.K)
    (hn : -((P.HC + P.K : ℕ) : ℤ) ≤ o ∧ o < ((P.HC + P.K : ℕ) : ℤ)) : headOffT L s o = o + xdisp s := by
  have hL0 : 0 < L := by omega
  have hLz : (4 * ((P.HC : ℤ) + P.K) + 4 : ℤ) ≤ L := by exact_mod_cast hL
  have hxs := xdisp_bounds s
  rw [hlen] at hxs
  push_cast at hn
  rw [headOffT_eq ho, qoffZ_of_bounds hL0 (by omega) (by omega)]

/-- A start far from the seam: the head offset is far from the seam. -/
theorem head_far_start {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L) {s : List (ℕ × Bool)} {o : ℤ}
    (ho : qoffZ L o = o) (hlen : s.length = P.K)
    (hn : ¬ (-((P.HC + P.K : ℕ) : ℤ) ≤ o ∧ o < ((P.HC + P.K : ℕ) : ℤ))) :
    ¬ (-(P.HC : ℤ) ≤ headOffT L s o ∧ headOffT L s o < P.HC) := by
  have hL0 : 0 < L := by omega
  have hLz : (4 * ((P.HC : ℤ) + P.K) + 4 : ℤ) ≤ L := by exact_mod_cast hL
  have hb := renorm_bounds hL0 ho
  have hxs := xdisp_bounds s
  rw [hlen] at hxs
  push_cast at hn
  rw [headOffT_eq ho]
  rcases qoffZ_cases hL0 (b := o + xdisp s) (by omega) (by omega) with ⟨-, -, c⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩
  · rw [c]; omega
  · rw [c2]; omega
  · rw [c2]; omega

end CertSoundT

open scoped Classical in
theorem certT_startSum (hc : CertOKT P nk nG bk bH) {L : ℕ} (hL : 4 * (P.HC + P.K) + 4 ≤ L) {o : ℤ}
    (ho : qoffZ L o = o) :
    ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) *
      ∑ s ∈ (pats 2 P.K).filter (fun s => IsStT P nk nG bk bH L s o),
        wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) s * (HofT P nk nG bk bH L s o : ℝ) ≤
      ((P.K0n : ℝ) / P.K0d) * P.Hmin := by
  have hHC2 := hc.hHC2
  have hK2 : (P.K : ℤ) ≤ 1023 := by exact_mod_cast K_le hc
  -- the offset of the start check
  let near : Prop := -((P.HC + P.K : ℕ) : ℤ) ≤ o ∧ o < ((P.HC + P.K : ℕ) : ℤ)
  let o0 : ℤ := if near then o else bigO
  have hst : startOKT P nk nG bk bH o0 = true := by
    by_cases hn : near
    · simp only [o0, if_pos hn]
      exact rangeAllT_of hc.startNear hn.1 (by have := hn.2; push_cast at this ⊢; omega)
    · simp only [o0, if_neg hn]
      exact hc.startBig
  -- (1) the bound in integers, state by state
  have hnat : ∑ s ∈ (pats 2 P.K).filter (fun s => IsStT P nk nG bk bH L s o),
      wtN P s * HofT P nk nG bk bH L s o ≤ startSumT P nk nG bk bH o0 := by
    rw [startSumT_eq, ← Finset.sum_filter_add_sum_filter_not _
      (fun s => -(P.HC : ℤ) ≤ headOffT L s o ∧ headOffT L s o < P.HC)]
    apply add_le_add
    · -- near heads: the near records
      apply Finset.sum_le_sum_of_injOn (fun s => (lookup nk (nearKey s (headOffT L s o))).getD 0)
      · intro s hs t ht hst'
        simp only [Finset.mem_coe, Finset.mem_filter] at hs ht
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨⟨-, htS⟩, htn⟩ := ht
        obtain ⟨-, hslen, hsdir, hsp⟩ := hsS
        obtain ⟨-, htlen, htdir, htp⟩ := htS
        rw [potT_near P nk nG bk bH hsn.1 hsn.2, Option.isSome_map] at hsp
        rw [potT_near P nk nG bk bH htn.1 htn.2, Option.isSome_map] at htp
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp
        obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp htp
        simp only [hj, hj', Option.getD_some] at hst'
        subst hst'
        have h1 := (lookup_some hj).2
        have h2 := (lookup_some hj').2
        have e1 := (nearKey_decode hslen hsdir (h := headOffT L s o) (by omega) (by omega)).1
        have e2 := (nearKey_decode htlen htdir (h := headOffT L t o) (by omega) (by omega)).1
        rw [← h1] at e1
        rw [← h2] at e2
        exact e1.symm.trans e2
      · intro j hj
        simp only [Finset.mem_image, Finset.mem_filter] at hj
        obtain ⟨s, ⟨⟨-, hsS⟩, hsn⟩, rfl⟩ := hj
        obtain ⟨-, -, -, hsp⟩ := hsS
        rw [potT_near P nk nG bk bH hsn.1 hsn.2, Option.isSome_map] at hsp
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp
        simp only [hj, Option.getD_some, Finset.mem_range]
        exact (lookup_some hj).1
      · intro s hs
        simp only [Finset.mem_filter] at hs
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨ho', hslen, hsdir, hsp⟩ := hsS
        have hsp' := hsp
        rw [potT_near P nk nG bk bH hsn.1 hsn.2, Option.isSome_map] at hsp'
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp'
        have hk := (lookup_some hj).2
        obtain ⟨d1, d2⟩ := nearKey_decode hslen hsdir (h := headOffT L s o) (by omega) (by omega)
        simp only [hj, Option.getD_some]
        unfold cN
        rw [hk, d1, d2]
        have hcond : headOffT L s o - xdisp s = o0 := by
          by_cases hn : near
          · simp only [o0, if_pos hn]
            rw [head_exact_start hL ho hslen hn]
            ring
          · exact absurd hsn (head_far_start hL ho hslen hn)
        rw [if_pos hcond]
        apply le_of_eq
        congr 1
        unfold HofT
        rw [potT_near P nk nG bk bH hsn.1 hsn.2, hj]
        rfl
      · intro _ _ _
        exact Nat.zero_le _
    · -- far heads: the bulk records
      apply Finset.sum_le_sum_of_injOn (fun s => (lookup bk (keyOf 2 s)).getD 0)
      · intro s hs t ht hst'
        simp only [Finset.mem_coe, Finset.mem_filter] at hs ht
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨⟨-, htS⟩, htn⟩ := ht
        obtain ⟨-, hslen, hsdir, hsp⟩ := hsS
        obtain ⟨-, htlen, htdir, htp⟩ := htS
        rw [potT_far P nk nG bk bH hsn, Option.isSome_map] at hsp
        rw [potT_far P nk nG bk bH htn, Option.isSome_map] at htp
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp
        obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp htp
        simp only [hj, hj', Option.getD_some] at hst'
        subst hst'
        exact keyOf_inj (by norm_num) hslen htlen hsdir htdir ((lookup_some hj).2.symm.trans (lookup_some hj').2)
      · intro j hj
        simp only [Finset.mem_image, Finset.mem_filter] at hj
        obtain ⟨s, ⟨⟨-, hsS⟩, hsn⟩, rfl⟩ := hj
        obtain ⟨-, -, -, hsp⟩ := hsS
        rw [potT_far P nk nG bk bH hsn, Option.isSome_map] at hsp
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp
        simp only [hj, Option.getD_some, Finset.mem_range]
        exact (lookup_some hj).1
      · intro s hs
        simp only [Finset.mem_filter] at hs
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨-, hslen, hsdir, hsp⟩ := hsS
        have hsp' := hsp
        rw [potT_far P nk nG bk bH hsn, Option.isSome_map] at hsp'
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp'
        have hk := (lookup_some hj).2
        simp only [hj, Option.getD_some]
        unfold cB
        rw [hk, decodeKey_keyOf (by norm_num) P.K s hslen hsdir]
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
        congr 1
        unfold HofT
        rw [potT_far P nk nG bk bH hsn, hj]
        rfl
      · intro _ _ _
        exact Nat.zero_le _
  -- (2) in reals
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hc.hQ
  have hKr : (0 : ℝ) < P.K0d := by exact_mod_cast hc.hK0d
  have hreal : ∑ s ∈ (pats 2 P.K).filter (fun s => IsStT P nk nG bk bH L s o),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) s * (HofT P nk nG bk bH L s o : ℝ) =
      ((∑ s ∈ (pats 2 P.K).filter (fun s => IsStT P nk nG bk bH L s o),
        wtN P s * HofT P nk nG bk bH L s o : ℕ) : ℝ) / (P.Q : ℝ) ^ P.K := by
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
  have hst' : (P.wE + P.wC) * startSumT P nk nG bk bH o0 * P.K0d ≤ P.K0n * P.Hmin * P.Q ^ (P.K + 1) := by
    unfold startOKT at hst
    simpa using hst
  have hst_r : ((P.wE : ℝ) + P.wC) * (startSumT P nk nG bk bH o0 : ℝ) * P.K0d ≤
      P.K0n * P.Hmin * (P.Q : ℝ) ^ (P.K + 1) := by exact_mod_cast hst'
  have hnat_r : ((∑ s ∈ (pats 2 P.K).filter (fun s => IsStT P nk nG bk bH L s o),
      wtN P s * HofT P nk nG bk bH L s o : ℕ) : ℝ) ≤ (startSumT P nk nG bk bH o0 : ℝ) := by exact_mod_cast hnat
  rw [hreal]
  calc ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) *
        (((∑ s ∈ (pats 2 P.K).filter (fun s => IsStT P nk nG bk bH L s o),
          wtN P s * HofT P nk nG bk bH L s o : ℕ) : ℝ) / (P.Q : ℝ) ^ P.K)
      ≤ ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) * ((startSumT P nk nG bk bH o0 : ℝ) / (P.Q : ℝ) ^ P.K) := by
        gcongr
    _ = ((P.wE : ℝ) + P.wC) * (startSumT P nk nG bk bH o0 : ℝ) / (P.Q : ℝ) ^ (P.K + 1) := by
        field_simp
        ring
    _ ≤ ((P.K0n : ℝ) / P.K0d) * P.Hmin := by
        rw [div_le_iff₀ (by positivity), show (P.K0n : ℝ) / P.K0d * P.Hmin * (P.Q : ℝ) ^ (P.K + 1) =
          (P.K0n * P.Hmin * (P.Q : ℝ) ^ (P.K + 1)) / P.K0d by ring, le_div_iff₀ hKr]
        exact hst_r

end Cert

end QEC
