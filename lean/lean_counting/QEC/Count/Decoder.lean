import QEC.Count.Defs
import QEC.Graph.PathExists

/-!
# Minimum-weight decoding with uniform weights: the failure path, half-weight, the exchange lemma

* `exists_phiMinFail`: if some minimum-weight correction fails, there is a failing one of least `Φ`.
* `failure_path`: a failing correction gives a simple path from `b1` to `b2` in `E ∆ C`.
* `half_weight_unif`: on such a path `γ` (any edge set with empty detector boundary), `|γ \ E| ≤ |γ ∩ E|`.
* `exchange`: for a failing minimum-weight correction `C` of least `Φ`, distinct edges `X ⊆ C`, `Y` disjoint from
  `C`, and an edge list `P` of the graph with the detector parity of `X ++ Y`, none of them at `b1`:
  `|X| ≤ |Y| + |P|`, and if equality holds and `P` has no repeated edge, `Φ(X) ≤ Φ(Y) + Φ(P)`. This one lemma gives
  the rules (M) and (J) (first part, with `Y` = the E-edges of the window or `Y = []`) and (P_M), (P_J), (S)
  (second part).
-/

namespace QEC

open Finset
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_phiMinFail (Eg : Finset (Sym2 (Vx V))) (Φ : Sym2 (Vx V) → ℤ) {E : Finset (Sym2 (Vx V))}
    (h : ∃ C, IsMinCorr Eg (bd E) C ∧ FailsB E C) : ∃ C, IsPhiMinFail Eg Φ E C := by
  classical
  set S := Eg.powerset.filter (fun C => IsMinCorr Eg (bd E) C ∧ FailsB E C) with hS
  obtain ⟨C0, hC0⟩ := h
  have hne : S.Nonempty := ⟨C0, by simp only [hS, mem_filter, mem_powerset]; exact ⟨hC0.1.1, hC0⟩⟩
  obtain ⟨C, hCS, hmin⟩ := S.exists_min_image (PhiS Φ) hne
  simp only [hS, mem_filter, mem_powerset] at hCS
  refine ⟨C, hCS.2.1, hCS.2.2, fun C' hC' hf' => hmin C' ?_⟩
  simp only [hS, mem_filter, mem_powerset]
  exact ⟨hC'.1, hC', hf'⟩

/-- A failing correction contains, together with the error, a simple path from `b1` to `b2`. -/
theorem failure_path {Eg E C : Finset (Sym2 (Vx V))} (hdiag : ∀ e ∈ Eg, ¬ e.IsDiag) (hE : E ⊆ Eg)
    (hC : IsMinCorr Eg (bd E) C) (hf : FailsB E C) : ∃ l, IsSPath (decGraph (E ∆ C)) .b1 .b2 l := by
  apply exists_path_of_odd
  · intro e he
    rcases Finset.mem_union.mp (Finset.symmDiff_subset_union he) with h | h
    · exact hdiag e (hE h)
    · exact hdiag e (hC.1 h)
  · intro v
    rw [← Nat.not_odd_iff_even, odd_vdeg_symmDiff, not_not]
    have := congrArg (fun s => v ∈ s) hC.2.1
    simp only [mem_bd] at this
    rw [this]
  · rw [odd_vdeg_symmDiff]
    intro h
    exact hf h.symm

/-- Half-weight with uniform weights (DKLP): a minimum-weight correction meets a cycle-free swap set `γ ⊆ E ∆ C`
(empty detector boundary) in at most as many edges as the error does. -/
theorem half_weight_unif {Eg C : Finset (Sym2 (Vx V))} {A : Finset V} (hC : IsMinCorr Eg A C)
    {γ E : Finset (Sym2 (Vx V))} (hγ : γ ⊆ Eg) (hbd : bd γ = ∅) (hsub : γ ⊆ E ∆ C) : #(γ \ E) ≤ #(γ ∩ E) := by
  obtain ⟨hCE, hCA, hmin⟩ := hC
  have hvalid : C ∆ γ ⊆ Eg := fun e he =>
    (Finset.mem_union.mp (Finset.symmDiff_subset_union he)).elim (fun h => hCE h) (fun h => hγ h)
  have hbdA : bd (C ∆ γ) = A := by
    rw [bd_symmDiff, hbd, ← Finset.bot_eq_empty, symmDiff_bot, hCA]
  have hle := hmin _ hvalid hbdA
  have h1 := card_symmDiff_add C γ
  have h2 : γ \ E = γ ∩ C := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨hg, hn⟩
      refine ⟨hg, ?_⟩
      rcases Finset.mem_symmDiff.mp (hsub hg) with h | h
      · exact absurd h.1 hn
      · exact h.1
    · rintro ⟨hg, hc⟩
      refine ⟨hg, fun he => ?_⟩
      rcases Finset.mem_symmDiff.mp (hsub hg) with h | h
      · exact h.2 hc
      · exact h.2 he
  have h3 : γ ∩ E = γ \ C := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨hg, he⟩
      refine ⟨hg, fun hc => ?_⟩
      rcases Finset.mem_symmDiff.mp (hsub hg) with h | h
      · exact h.2 hc
      · exact h.2 he
    · rintro ⟨hg, hc⟩
      refine ⟨hg, ?_⟩
      rcases Finset.mem_symmDiff.mp (hsub hg) with h | h
      · exact h.1
      · exact absurd h.1 hc
  have h4 := Finset.card_sdiff_add_card_inter γ C
  rw [Finset.inter_comm C γ] at h1
  rw [h2, h3]
  omega

/-- The symmetric difference of disjoint sets is their union. -/
theorem Dec_symmDiff_eq_union {α : Type*} [DecidableEq α] {A B : Finset α} (h : Disjoint A B) :
    A ∆ B = A ∪ B := by
  ext e
  simp only [Finset.mem_symmDiff, Finset.mem_union]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (h1 | h1)
    · exact Or.inl ⟨h1, fun h2 => Finset.disjoint_left.mp h h1 h2⟩
    · exact Or.inr ⟨h1, fun h2 => Finset.disjoint_left.mp h h2 h1⟩

omit [Fintype V] in
/-- Toggling edges that do not contain `b1` keeps the degree at `b1`. -/
theorem Dec_vdeg_b1_symmDiff {C T : Finset (Sym2 (Vx V))} (hT : ∀ e ∈ T, Vx.b1 ∉ e) :
    vdeg (C ∆ T) Vx.b1 = vdeg C Vx.b1 := by
  unfold vdeg
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_symmDiff]
  constructor
  · rintro ⟨h | h, hb⟩
    · exact ⟨h.1, hb⟩
    · exact absurd hb (hT e h.1)
  · rintro ⟨hc, hb⟩
    exact ⟨Or.inl ⟨hc, fun ht => hT e ht hb⟩, hb⟩

/-- **The exchange lemma.** -/
theorem exchange {Eg : Finset (Sym2 (Vx V))} {Φ : Sym2 (Vx V) → ℤ} {E C : Finset (Sym2 (Vx V))}
    (hC : IsPhiMinFail Eg Φ E C) {X Y P : List (Sym2 (Vx V))} (hXY : (X ++ Y).Nodup) (hX : ∀ e ∈ X, e ∈ C)
    (hY : ∀ e ∈ Y, e ∉ C) (hg : ∀ e ∈ X ++ Y ++ P, e ∈ Eg) (hb1 : ∀ e ∈ X ++ Y ++ P, Vx.b1 ∉ e)
    (hodd : oddD P = oddD (X ++ Y)) :
    X.length ≤ Y.length + P.length ∧
      (X.length = Y.length + P.length → P.Nodup → (X.map Φ).sum ≤ (Y.map Φ).sum + (P.map Φ).sum) := by
  classical
  obtain ⟨⟨hCE, hCA, hmin⟩, hfail, hphi⟩ := hC
  have hXn : X.Nodup := (List.nodup_append.mp hXY).1
  have hYn : Y.Nodup := (List.nodup_append.mp hXY).2.1
  have hσg : ∀ e ∈ (X ++ Y).toFinset, e ∈ Eg := fun e he =>
    hg e (List.mem_append_left _ (List.mem_toFinset.mp he))
  have hPg : ∀ e ∈ oddE P, e ∈ Eg := fun e he =>
    hg e (List.mem_append_right _ (List.mem_toFinset.mp (oddE_subset P he)))
  have hb1σ : ∀ e ∈ (X ++ Y).toFinset, Vx.b1 ∉ e := fun e he =>
    hb1 e (List.mem_append_left _ (List.mem_toFinset.mp he))
  have hb1P : ∀ e ∈ oddE P, Vx.b1 ∉ e := fun e he =>
    hb1 e (List.mem_append_right _ (List.mem_toFinset.mp (oddE_subset P he)))
  -- the new correction
  have hC'g : (C ∆ (X ++ Y).toFinset) ∆ oddE P ⊆ Eg := by
    intro e he
    rcases Finset.mem_union.mp (Finset.symmDiff_subset_union he) with h | h
    · rcases Finset.mem_union.mp (Finset.symmDiff_subset_union h) with h' | h'
      · exact hCE h'
      · exact hσg e h'
    · exact hPg e h
  have hbdσ : bd (X ++ Y).toFinset = oddD (X ++ Y) := by
    rw [← oddE_of_nodup hXY, bd_oddE]
  have hC'bd : bd ((C ∆ (X ++ Y).toFinset) ∆ oddE P) = bd E := by
    rw [bd_symmDiff, bd_symmDiff, hbdσ, bd_oddE, hodd, symmDiff_assoc, symmDiff_self, symmDiff_bot, hCA]
  -- sizes
  have hCσ : C ∩ (X ++ Y).toFinset = X.toFinset := by
    ext e
    simp only [Finset.mem_inter, List.mem_toFinset, List.mem_append]
    constructor
    · rintro ⟨hc, hx | hy⟩
      · exact hx
      · exact absurd hc (hY e hy)
    · intro hx
      exact ⟨hX e hx, Or.inl hx⟩
  have hcardC1 : #(C ∆ (X ++ Y).toFinset) + X.length = #C + Y.length := by
    have h := card_symmDiff_add C (X ++ Y).toFinset
    rw [hCσ, List.toFinset_card_of_nodup hXn, List.toFinset_card_of_nodup hXY, List.length_append] at h
    omega
  have hoddle : #(oddE P) ≤ P.length := (Finset.card_le_card (oddE_subset P)).trans (List.toFinset_card_le P)
  have hC'le : #((C ∆ (X ++ Y).toFinset) ∆ oddE P) ≤ #(C ∆ (X ++ Y).toFinset) + #(oddE P) :=
    (Finset.card_le_card Finset.symmDiff_subset_union).trans (Finset.card_union_le _ _)
  have hle := hmin _ hC'g hC'bd
  refine ⟨by omega, ?_⟩
  intro heq hPn
  -- equality: the alternative is disjoint from `C ∆ σ`, and the new correction is a failing minimizer
  have hoddP : oddE P = P.toFinset := oddE_of_nodup hPn
  have hcardP : #P.toFinset = P.length := List.toFinset_card_of_nodup hPn
  have h5 := card_symmDiff_add (C ∆ (X ++ Y).toFinset) (oddE P)
  rw [hoddP, hcardP] at h5
  rw [hoddP] at hle
  have hint0 : #((C ∆ (X ++ Y).toFinset) ∩ P.toFinset) = 0 := by omega
  have hcardC' : #((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) = #C := by omega
  have hdisjP : Disjoint (C ∆ (X ++ Y).toFinset) P.toFinset :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hint0)
  have hC'eq : (C ∆ (X ++ Y).toFinset) ∆ P.toFinset = (C ∆ (X ++ Y).toFinset) ∪ P.toFinset :=
    Dec_symmDiff_eq_union hdisjP
  rw [hoddP] at hC'g hC'bd
  have hminC' : IsMinCorr Eg (bd E) ((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) :=
    ⟨hC'g, hC'bd, fun C'' h1 h2 => by rw [hcardC']; exact hmin C'' h1 h2⟩
  have hb1P' : ∀ e ∈ P.toFinset, Vx.b1 ∉ e := by rw [← hoddP]; exact hb1P
  have hvd : vdeg ((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) Vx.b1 = vdeg C Vx.b1 := by
    rw [Dec_vdeg_b1_symmDiff hb1P', Dec_vdeg_b1_symmDiff hb1σ]
  have hfailC' : FailsB E ((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) := by
    unfold FailsB at hfail ⊢
    rw [hvd]
    exact hfail
  have hle2 := hphi _ hminC' hfailC'
  -- `Φ` of the new correction
  have hdisjXY : Disjoint X.toFinset Y.toFinset := by
    rw [Finset.disjoint_left]
    intro e hx hy
    exact (List.disjoint_of_nodup_append hXY) (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy)
  have hC1eq : C ∆ (X ++ Y).toFinset = (C \ X.toFinset) ∪ Y.toFinset := by
    ext e
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, List.mem_append]
    constructor
    · rintro (⟨hc, hn⟩ | ⟨hxy, hc⟩)
      · left; exact ⟨hc, fun hx => hn (Or.inl hx)⟩
      · rcases hxy with hx | hy
        · exact absurd (hX e hx) hc
        · right; exact hy
    · rintro (⟨hc, hx⟩ | hy)
      · left; exact ⟨hc, fun h => h.elim hx (fun hy => hY e hy hc)⟩
      · right; exact ⟨Or.inr hy, hY e hy⟩
  have hXs : X.toFinset ⊆ C := fun e he => hX e (List.mem_toFinset.mp he)
  have hphiC1 : PhiS Φ (C ∆ (X ++ Y).toFinset) = PhiS Φ C - (X.map Φ).sum + (Y.map Φ).sum := by
    unfold PhiS
    rw [hC1eq, Finset.sum_union (by
      rw [Finset.disjoint_left]
      intro e he hy
      exact hY e (List.mem_toFinset.mp hy) (Finset.mem_sdiff.mp he).1)]
    rw [Finset.sum_sdiff_eq_sub hXs, List.sum_toFinset _ hXn, List.sum_toFinset _ hYn]
  have hphiC' : PhiS Φ ((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) =
      PhiS Φ (C ∆ (X ++ Y).toFinset) + (P.map Φ).sum := by
    unfold PhiS
    rw [hC'eq, Finset.sum_union hdisjP, List.sum_toFinset _ hPn]
  rw [hphiC', hphiC1] at hle2
  linarith

end QEC
