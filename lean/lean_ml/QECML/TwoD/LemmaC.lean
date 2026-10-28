import QECML.TwoD.LemmaB

/-!
# Lemma C (failure paths; step (C) of the paper's proof outline)

The graph `Γ` (`gadj`) has the checks, the two boundaries `b₁`, `b₂` and the families as nodes. Its edges are the
bulk edges of `C_top` (between checks), the half-edges of `C_top` (check to `b₁` or `b₂`), "an odd check of `Ω`
lies in a block of the family" (check to family), and "`Y_𝓕` has odd degree at `b_i`" (family to `b_i`).

* `lemmaC`: if S3' fails, `b₁` and `b₂` are joined by a path of `Γ`. Proof: otherwise the nodes reachable from `b₁`
  give `pcls C_top = Σ_𝓕 pcls Y_𝓕` (handshake for `C_top` on the reachable checks, Lemma B for each reachable
  family), so the class of `E + C` would vanish (`pcls_decomp`).

A path from `b₁` to `b₂` passes through families joined by paths of `C_top`, or through a family adjacent to both
boundaries (a spanning family): the cases (T2) and (T1).
-/

open Finset Classical

namespace QECML

/-- The parity of an edge set on the top half-edges. -/
def pclsT (w h : ℕ) : (PEdge w h → ZMod 2) →+ ZMod 2 where
  toFun e := ∑ x, e (.top x)
  map_zero' := by simp
  map_add' e e' := by simp [Finset.sum_add_distrib]

theorem pclsT_apply {w h : ℕ} (e : PEdge w h → ZMod 2) : pclsT w h e = ∑ x, e (.top x) := rfl

/-- A sum over the edges by constructor. -/
theorem sum_pedge {w h : ℕ} {M : Type*} [AddCommMonoid M] (F : PEdge w h → M) :
    ∑ f, F f = (∑ p : Fin w × Fin (h + 1), F (.hor p.1 p.2)) + ((∑ p : Fin (w + 1) × Fin h, F (.ver p.1 p.2)) +
      ((∑ x, F (.bot x)) + ∑ x, F (.top x))) := by
  rw [← PEdge.equivSum.symm.sum_comp]
  simp only [Fintype.sum_sum_type]
  rfl

/-- **Handshake on a closed set of checks**: if `Q` contains with every check the other end of each bulk edge of `X`
at it, then the odd checks of `X` in `Q` have the parity of the half-edges of `X` at checks of `Q`. -/
theorem sum_psyn_restrict {w h : ℕ} (X : PEdge w h → ZMod 2) (Q : Set (PVert w h))
    (hQ : ∀ (f : PEdge w h) (u v : PVert w h), f.ends = {u, v} → u ≠ v → X f ≠ 0 → u ∈ Q → v ∈ Q) :
    ∑ v, (if v ∈ Q then psyn w h X v else 0) =
      (∑ x, if (x, 0) ∈ Q then X (.bot x) else 0) + ∑ x, if (x, Fin.last h) ∈ Q then X (.top x) else 0 := by
  have hcount : ∀ f : PEdge w h, (∑ v, if v ∈ Q then (if v ∈ f.ends then (1 : ZMod 2) else 0) * X f else 0) =
      X f * (((f.ends.filter (· ∈ Q)).card : ℕ) : ZMod 2) := by
    intro f
    rw [mul_comm]
    have : ∀ v, (if v ∈ Q then (if v ∈ f.ends then (1 : ZMod 2) else 0) * X f else 0) =
        (if v ∈ f.ends.filter (· ∈ Q) then (1 : ZMod 2) else 0) * X f := by
      intro v
      by_cases hvQ : v ∈ Q <;> by_cases hvf : v ∈ f.ends <;> simp [hvQ, hvf]
    rw [Finset.sum_congr rfl fun v _ => this v, ← Finset.sum_mul, Finset.sum_boole]
    congr 3
    ext x
    simp
  have hpair : ∀ (f : PEdge w h) (u v : PVert w h), f.ends = {u, v} → u ≠ v →
      X f * (((f.ends.filter (· ∈ Q)).card : ℕ) : ZMod 2) = 0 := by
    intro f u v hf huv
    by_cases hX : X f = 0
    · rw [hX, zero_mul]
    · have huQ : u ∈ Q ↔ v ∈ Q := ⟨hQ f u v hf huv hX, hQ f v u (by rw [hf, Finset.pair_comm]) huv.symm hX⟩
      rw [hf]
      by_cases hu : u ∈ Q
      · have hv := huQ.1 hu
        rw [Finset.filter_true_of_mem (by simp [hu, hv]), Finset.card_pair huv]
        have : ((2 : ℕ) : ZMod 2) = 0 := by decide
        rw [this, mul_zero]
      · have hv : v ∉ Q := fun hv => hu (huQ.2 hv)
        rw [Finset.filter_false_of_mem (by simp [hu, hv]), Finset.card_empty]
        simp
  calc ∑ v, (if v ∈ Q then psyn w h X v else 0)
      = ∑ v, ∑ f, (if v ∈ Q then (if v ∈ f.ends then (1 : ZMod 2) else 0) * X f else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [psyn_apply]
        split_ifs <;> simp
    _ = ∑ f, X f * (((f.ends.filter (· ∈ Q)).card : ℕ) : ZMod 2) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun f _ => hcount f
    _ = _ := by
        rw [sum_pedge]
        have h1 : ∑ p : Fin w × Fin (h + 1),
            X (.hor p.1 p.2) * ((((PEdge.hor p.1 p.2).ends.filter (· ∈ Q)).card : ℕ) : ZMod 2) = 0 :=
          Finset.sum_eq_zero fun p _ => hpair _ _ _ rfl fun he => by
            simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at he
            omega
        have h2 : ∑ p : Fin (w + 1) × Fin h,
            X (.ver p.1 p.2) * ((((PEdge.ver p.1 p.2).ends.filter (· ∈ Q)).card : ℕ) : ZMod 2) = 0 :=
          Finset.sum_eq_zero fun p _ => hpair _ _ _ rfl fun he => by
            simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at he
            omega
        rw [h1, h2, zero_add, zero_add]
        congr 1
        · refine Finset.sum_congr rfl fun x _ => ?_
          simp only [PEdge.ends, Finset.filter_singleton]
          split_ifs <;> simp
        · refine Finset.sum_congr rfl fun x _ => ?_
          simp only [PEdge.ends, Finset.filter_singleton]
          split_ifs <;> simp

/-- **Handshake**: the odd checks of an edge set have the parity of its half-edges. -/
theorem sum_psyn {w h : ℕ} (X : PEdge w h → ZMod 2) : ∑ v, psyn w h X v = pcls w h X + pclsT w h X := by
  have := sum_psyn_restrict X Set.univ (fun _ _ _ _ _ _ _ => Set.mem_univ _)
  simpa [pcls_apply, pclsT_apply] using this

namespace S3Geom

/-- The nodes of `Γ`: checks, the two boundaries (`false` = `b₁`, `true` = `b₂`), families (block sets). -/
abbrev GNode (G : S3Geom) : Type := G.V ⊕ Bool ⊕ Set G.Block

end S3Geom

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- The top-level syndrome `Ω` of the decoder on the syndrome of `E`. -/
noncomputable def om (a0 a1 : ℕ) (E : G.Ed → ZMod 2) : G.V → ZMod 2 := S3Geom.omegaSyn (S.resid E) a0 a1

/-- The top-level correction `C_top`. -/
noncomputable def ctop (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) : G.Ed → ZMod 2 :=
  Z.solve Set.univ (S.om a0 a1 E)

theorem psyn_ctop (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) :
    psyn G.w G.h (S.ctop a0 a1 Z E) = S.om a0 a1 E :=
  Z.correct _ _ (S3Geom.realizable_of_rough S3Geom.conn_univ (Set.mem_univ (⟨0, by omega⟩, ⟨0, by omega⟩))
    (Or.inl rfl) fun v _ => Set.mem_univ v)

/-- An odd check of `Ω` lies in a bad block. -/
theorem badD_of_om {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {v : G.V} (hv : S.om a0 a1 E v ≠ 0) :
    S.badD E (G.blockOf v) := by
  simp only [om, S3Geom.omegaSyn] at hv
  split_ifs at hv with h
  · obtain ⟨⟨u, hu, hD⟩, _⟩ := h.1
    exact Or.inr (Or.inl ⟨u, hu, hD⟩)
  · exact absurd rfl hv

/-- One-directional adjacency of `Γ`. -/
def gadj0 (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) : G.GNode → G.GNode → Prop
  | .inl u, .inl v => ∃ e : G.Ed, e.ends = {u, v} ∧ u ≠ v ∧ S.ctop a0 a1 Z E e ≠ 0
  | .inl u, .inr (.inl false) => ∃ x, u = (x, 0) ∧ S.ctop a0 a1 Z E (.bot x) ≠ 0
  | .inl u, .inr (.inl true) => ∃ x, u = (x, Fin.last _) ∧ S.ctop a0 a1 Z E (.top x) ≠ 0
  | .inl u, .inr (.inr Fm) => Fm ∈ S.families a0 a1 E ∧ G.blockOf u ∈ Fm ∧ S.om a0 a1 E u ≠ 0
  | .inr (.inr Fm), .inr (.inl false) =>
      Fm ∈ S.families a0 a1 E ∧ pcls G.w G.h (S.Yfam a0 a1 Z E Fm) ≠ 0
  | .inr (.inr Fm), .inr (.inl true) =>
      Fm ∈ S.families a0 a1 E ∧ pclsT G.w G.h (S.Yfam a0 a1 Z E Fm) ≠ 0
  | _, _ => False

/-- The adjacency of `Γ`. -/
def gadj (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) (x y : G.GNode) : Prop :=
  S.gadj0 a0 a1 Z E x y ∨ S.gadj0 a0 a1 Z E y x

/-- **Lemma C**: if S3' fails, the boundaries `b₁` and `b₂` are joined in `Γ`. -/
theorem lemmaC {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (Z : Solver G) {E : G.Ed → ZMod 2}
    (hfail : failsOn (S3Geom.S3dec S a0 a1 Z) E) :
    Relation.ReflTransGen (S.gadj a0 a1 Z E) (.inr (.inl false)) (.inr (.inl true)) := by
  by_contra hno
  let R : G.GNode → Prop := fun x => Relation.ReflTransGen (S.gadj a0 a1 Z E) (.inr (.inl false)) x
  have hstep : ∀ x y, R x → S.gadj a0 a1 Z E x y → R y := fun x y hx hxy => hx.tail hxy
  have hR0 : R (.inr (.inl false)) := .refl
  let Q : Set G.V := {v | R (.inl v)}
  have hQclosed : ∀ (f : G.Ed) (u v : G.V), f.ends = {u, v} → u ≠ v → S.ctop a0 a1 Z E f ≠ 0 → u ∈ Q → v ∈ Q :=
    fun f u v hf huv hX hu => hstep _ _ hu (Or.inl ⟨f, hf, huv, hX⟩)
  have hbotQ : ∀ x, S.ctop a0 a1 Z E (.bot x) ≠ 0 → ((x, 0) : G.V) ∈ Q :=
    fun x hx => hstep _ _ hR0 (Or.inr ⟨x, rfl, hx⟩)
  have htopQ : ∀ x, S.ctop a0 a1 Z E (.top x) ≠ 0 → ((x, Fin.last _) : G.V) ∉ Q :=
    fun x hx hQx => hno (hstep _ _ hQx (Or.inl ⟨x, rfl, hx⟩))
  have hfamb1 : ∀ Fm ∈ S.families a0 a1 E, pcls G.w G.h (S.Yfam a0 a1 Z E Fm) ≠ 0 → R (.inr (.inr Fm)) :=
    fun Fm hFm h => hstep _ _ hR0 (Or.inr ⟨hFm, h⟩)
  have hfamb2 : ∀ Fm ∈ S.families a0 a1 E, R (.inr (.inr Fm)) →
      pclsT G.w G.h (S.Yfam a0 a1 Z E Fm) = 0 :=
    fun Fm hFm hRF => by
      by_contra h
      exact hno (hstep _ _ hRF (Or.inl ⟨hFm, h⟩))
  have hcheckfam : ∀ Fm ∈ S.families a0 a1 E, ∀ u : G.V, G.blockOf u ∈ Fm → S.om a0 a1 E u ≠ 0 →
      (u ∈ Q ↔ R (.inr (.inr Fm))) :=
    fun Fm hFm u hu hom => ⟨fun h => hstep _ _ h (Or.inl ⟨hFm, hu, hom⟩),
      fun h => hstep _ _ h (Or.inr ⟨hFm, hu, hom⟩)⟩
  -- the odd checks of `Ω` in `Q`, counted through `C_top`
  have hA1 : ∑ v, (if v ∈ Q then S.om a0 a1 E v else 0) = pcls G.w G.h (S.ctop a0 a1 Z E) := by
    have h := sum_psyn_restrict (S.ctop a0 a1 Z E) Q hQclosed
    rw [S.psyn_ctop] at h
    rw [h, pcls_apply]
    have hb : ∀ x, (if ((x, 0) : G.V) ∈ Q then S.ctop a0 a1 Z E (.bot x) else 0) = S.ctop a0 a1 Z E (.bot x) :=
      fun x => by
        by_cases hx : S.ctop a0 a1 Z E (.bot x) = 0
        · rw [hx]; simp
        · rw [ite_eq_left (hbotQ x hx)]
    have ht : ∀ x, (if ((x, Fin.last _) : G.V) ∈ Q then S.ctop a0 a1 Z E (.top x) else 0) = 0 :=
      fun x => by
        by_cases hx : S.ctop a0 a1 Z E (.top x) = 0
        · rw [hx]; simp
        · rw [ite_eq_right (htopQ x hx)]
    simp only [hb, ht, Finset.sum_const_zero, add_zero]
  -- the odd checks of `Ω` in `Q`, counted through the families
  have hpt : ∀ v, (if v ∈ Q then S.om a0 a1 E v else 0) = ∑ Fm ∈ S.families a0 a1 E,
      (if R (.inr (.inr Fm)) then G.restrictTo Fm (S.om a0 a1 E) v else 0) := by
    intro v
    by_cases hov : S.om a0 a1 E v = 0
    · rw [hov]
      simp [S3Geom.restrictTo, hov]
    · have hb := S.badD_of_om hov
      set Fm0 := S.family a0 a1 E (G.blockOf v)
      have hFm0 : Fm0 ∈ S.families a0 a1 E := S.family_mem_families hb
      have hv0 : G.blockOf v ∈ Fm0 := S.mem_family_self hb
      have hiff := hcheckfam Fm0 hFm0 v hv0 hov
      simp only [S3Geom.restrictTo, ← ite_and]
      by_cases hR : R (.inr (.inr Fm0))
      · rw [ite_eq_left (hiff.2 hR), sum_ite_unique]
        exact ⟨Fm0, ⟨hFm0, hR, hv0⟩, fun Fm ⟨hFm, _, hvF⟩ =>
          S.families_eq_of_mem hFm hFm0 hvF hv0⟩
      · rw [ite_eq_right (fun h => hR (hiff.1 h))]
        refine (Finset.sum_eq_zero fun Fm hFm => ?_).symm
        rw [ite_eq_right]
        rintro ⟨hRF, hvF⟩
        exact hR (S.families_eq_of_mem hFm hFm0 hvF hv0 ▸ hRF)
  have hA2 : ∑ v, (if v ∈ Q then S.om a0 a1 E v else 0) =
      ∑ Fm ∈ S.families a0 a1 E, pcls G.w G.h (S.Yfam a0 a1 Z E Fm) := by
    rw [Finset.sum_congr rfl fun v _ => hpt v, Finset.sum_comm]
    refine Finset.sum_congr rfl fun Fm hFm => ?_
    by_cases hR : R (.inr (.inr Fm))
    · simp only [hR, ↓reduceIte]
      rw [show G.restrictTo Fm (S.om a0 a1 E) = psyn G.w G.h (S.Yfam a0 a1 Z E Fm) from
        (S.psyn_Yfam ha0 Z hFm).symm, sum_psyn, hfamb2 Fm hFm hR, add_zero]
    · simp only [hR, ↓reduceIte, Finset.sum_const_zero]
      by_contra h
      exact hR (hfamb1 Fm hFm (Ne.symm h))
  -- then the class of `E + C` would vanish
  apply hfail
  refine ⟨S3Geom.S3dec_valid S a0 a1 Z (psyn G.w G.h E), ?_⟩
  have hdec := S.pcls_decomp (a1 := a1) ha0 Z E
  have hctop : pcls G.w G.h (Z.solve Set.univ (S3Geom.omegaSyn (S.resid E) a0 a1)) =
      ∑ Fm ∈ S.families a0 a1 E, pcls G.w G.h (S.Yfam a0 a1 Z E Fm) := by
    show pcls G.w G.h (S.ctop a0 a1 Z E) = _
    rw [← hA1, hA2]
  rw [hdec, hctop, zmod2_add_self]

end Stage1

end QECML
