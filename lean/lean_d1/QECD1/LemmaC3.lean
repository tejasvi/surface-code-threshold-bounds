import QECD1.LemmaB3

/-!
# Lemma C (failure path) on the 3D code

The 3D analogue of the 2D `TwoD/LemmaC`. The graph `Γ` (`gadj3`) has the checks, the two rough boundaries `b₁`
(bottom, `false`) and `b₂` (top, `true`), and the families as nodes. Its edges are the bulk edges of `C_top` (between
checks), the half-edges of `C_top` (check to `b₁` or `b₂`), "an odd check of `Ω` lies in a block of the family" (check
to family), and "`Y_𝓕` has odd class at `b₁` or `b₂`" (family to boundary).

* `sum_half3`: a sum over the half-edges splits into the bottom and the top half-edges, at all times.
* `sum_psyn3_restrict` (handshake on a closed set of checks): if `Q` contains, with each check, the other end of each
  bulk edge of `X` at it, then the odd checks of `X` in `Q` have the parity of the half-edges of `X` at checks of `Q`.
* `lemmaC3`: if the decoder fails, `b₁` and `b₂` are joined by a path of `Γ`. Otherwise the nodes reachable from `b₁`
  give `pcls3 C_top = Σ_𝓕 pcls3 Y_𝓕` (handshake for `C_top` on the reachable checks, Lemma B for each reachable
  family), so the class of `E + C` would vanish (`pcls3_decomp`).
-/

open Finset

namespace QECD1

open Classical

variable {T w h : ℕ}

/-- The parity of an edge set on the top half-edges, at all times. -/
noncomputable def pclsT3 (X : PEdge3 T w h → ZMod 2) : ZMod 2 := ∑ t : Fin (T + 1), ∑ x : Fin (w + 1), X (.top t x)

/-- **A sum over the half-edges** splits into the bottom and the top half-edges, at all times. -/
theorem sum_half3 {M : Type} [AddCommMonoid M] (g : PEdge3 T w h → M) :
    ∑ e ∈ Finset.univ.filter (fun e : PEdge3 T w h => e.isHalf), g e =
      ∑ t : Fin (T + 1), ∑ x : Fin (w + 1), g (.bot t x) + ∑ t : Fin (T + 1), ∑ x : Fin (w + 1), g (.top t x) := by
  have hS : Finset.univ.filter (fun e : PEdge3 T w h => e.isHalf) =
      (Finset.univ.image (fun p : Fin (T + 1) × Fin (w + 1) => PEdge3.bot (h := h) p.1 p.2)) ∪
        (Finset.univ.image (fun p : Fin (T + 1) × Fin (w + 1) => PEdge3.top (h := h) p.1 p.2)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
    cases e <;> simp [PEdge3.isHalf]
  have hdisj : Disjoint (Finset.univ.image (fun p : Fin (T + 1) × Fin (w + 1) => PEdge3.bot (h := h) p.1 p.2))
      (Finset.univ.image (fun p : Fin (T + 1) × Fin (w + 1) => PEdge3.top (h := h) p.1 p.2)) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨p, rfl⟩ := h1
    obtain ⟨q, hq⟩ := h2
    cases hq
  rw [hS, Finset.sum_union hdisj, Finset.sum_image fun p _ q _ hpq => by
      simp only [PEdge3.bot.injEq] at hpq
      exact Prod.ext hpq.1 hpq.2,
    Finset.sum_image fun p _ q _ hpq => by
      simp only [PEdge3.top.injEq] at hpq
      exact Prod.ext hpq.1 hpq.2, Fintype.sum_prod_type, Fintype.sum_prod_type]

/-- **Handshake**: the odd checks of an edge set have the parity of its half-edges. -/
theorem sum_psyn3_cls (X : PEdge3 T w h → ZMod 2) : ∑ v, psyn3 X v = pcls3 X + pclsT3 X := by
  rw [sum_psyn3, sum_half3]
  rfl

/-- **Handshake on a closed set of checks.** -/
theorem sum_psyn3_restrict (X : PEdge3 T w h → ZMod 2) (Q : Set (PVert3 T w h))
    (hQ : ∀ (f : PEdge3 T w h) (u v : PVert3 T w h), f.ends = {u, v} → u ≠ v → X f ≠ 0 → u ∈ Q → v ∈ Q) :
    ∑ v, (if v ∈ Q then psyn3 X v else 0) =
      (∑ t : Fin (T + 1), ∑ x : Fin (w + 1), if ((t, x, 0) : PVert3 T w h) ∈ Q then X (.bot t x) else 0) +
        ∑ t : Fin (T + 1), ∑ x : Fin (w + 1), if ((t, x, Fin.last h) : PVert3 T w h) ∈ Q then X (.top t x) else 0 := by
  -- count each edge at its ends in `Q`
  have h1 : ∑ v, (if v ∈ Q then psyn3 X v else 0) =
      ∑ e, ∑ v ∈ e.ends, (if v ∈ Q then X e else 0) := by
    have hv : ∀ v, (if v ∈ Q then psyn3 X v else 0) =
        ∑ e ∈ Finset.univ.filter (fun e : PEdge3 T w h => v ∈ e.ends), (if v ∈ Q then X e else 0) := by
      intro v
      unfold psyn3
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun v _ => hv v]
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun e => e.ends) (by intro v e; simp)]
  -- a bulk edge of `X` has both ends in `Q` or none
  have hbulk : ∀ e : PEdge3 T w h, ¬ e.isHalf → ∑ v ∈ e.ends, (if v ∈ Q then X e else 0) = 0 := by
    intro e he
    obtain ⟨u, v, huv, hends⟩ := Finset.card_eq_two.1 (card_ends_bulk e he)
    rw [hends, Finset.sum_pair huv]
    by_cases hX : X e = 0
    · simp [hX]
    · have hiff : u ∈ Q ↔ v ∈ Q := ⟨hQ e u v hends huv hX,
        hQ e v u (by rw [hends, Finset.pair_comm]) huv.symm hX⟩
      by_cases hu : u ∈ Q
      · rw [if_pos hu, if_pos (hiff.1 hu)]
        exact CharTwo.add_self_eq_zero _
      · rw [if_neg hu, if_neg (fun hv' => hu (hiff.2 hv')), add_zero]
  rw [h1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e : PEdge3 T w h => e.isHalf),
    Finset.sum_eq_zero (s := Finset.univ.filter (fun e : PEdge3 T w h => ¬ e.isHalf))
      (fun e he => hbulk e (Finset.mem_filter.1 he).2), add_zero, sum_half3]
  simp [PEdge3.ends]

/-- Failure of a correction decoder on the error `E`: a wrong syndrome, or a nonzero class of the residual. -/
def failsOn3 (dec : (PVert3 T w h → ZMod 2) → (PEdge3 T w h → ZMod 2)) (E : PEdge3 T w h → ZMod 2) : Prop :=
  ¬ (psyn3 (dec (psyn3 E)) = psyn3 E ∧ pcls3 (E + dec (psyn3 E)) = 0)

/-- The nodes of `Γ`: checks, the two boundaries (`false` = `b₁`, `true` = `b₂`), families (block sets). -/
abbrev GNode3 (T w h : ℕ) : Type := PVert3 T w h ⊕ Bool ⊕ Finset V3

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- The top-level syndrome `Ω` of the decoder on the syndrome of `E`. -/
noncomputable def om3 (E : PEdge3 T w h → ZMod 2) : PVert3 T w h → ZMod 2 := omega3 (residD3 S (psyn3 E))

/-- The top-level correction `C_top`. -/
noncomputable def ctop3 (E : PEdge3 T w h → ZMod 2) : PEdge3 T w h → ZMod 2 := Z.solve Set.univ (S.om3 E)

theorem psyn3_ctop3 (E : PEdge3 T w h → ZMod 2) : psyn3 (S.ctop3 Z E) = S.om3 E :=
  Z.correct _ _ (realizable_of_rough conn3_univ (Set.mem_univ (0, 0, 0)) (Or.inl rfl) fun v _ => Set.mem_univ v)

/-- An odd check of `Ω` lies in a block of the bad set. -/
theorem bad_of_om3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {v : PVert3 T w h} (hv : S.om3 E v ≠ 0) :
    blockOf3 v ∈ S.badSet ny E := by
  simp only [om3, omega3] at hv
  split_ifs at hv with hc
  · have h1 := hc.1
    rw [lev1Set3_eq] at h1
    exact S.levSet_sub _ ny E h1
  · exact absurd rfl hv

/-- One-directional adjacency of `Γ`. -/
def gadj0 (ny : ℕ) (E : PEdge3 T w h → ZMod 2) : GNode3 T w h → GNode3 T w h → Prop
  | .inl u, .inl v => ∃ e : PEdge3 T w h, e.ends = {u, v} ∧ u ≠ v ∧ S.ctop3 Z E e ≠ 0
  | .inl u, .inr (.inl false) => ∃ t x, u = (t, x, 0) ∧ S.ctop3 Z E (.bot t x) ≠ 0
  | .inl u, .inr (.inl true) => ∃ t x, u = (t, x, Fin.last h) ∧ S.ctop3 Z E (.top t x) ≠ 0
  | .inl u, .inr (.inr Fm) =>
      Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧ blockOf3 u ∈ Fm ∧ S.om3 E u ≠ 0
  | .inr (.inr Fm), .inr (.inl false) =>
      Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧ pcls3 (S.Yfam3 Z E Fm) ≠ 0
  | .inr (.inr Fm), .inr (.inl true) =>
      Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧ pclsT3 (S.Yfam3 Z E Fm) ≠ 0
  | _, _ => False

/-- The adjacency of `Γ`. -/
def gadj3 (ny : ℕ) (E : PEdge3 T w h → ZMod 2) (x y : GNode3 T w h) : Prop :=
  S.gadj0 Z ny E x y ∨ S.gadj0 Z ny E y x

/-- **Lemma C on the 3D code**: if S3' fails, the boundaries `b₁` and `b₂` are joined in `Γ`. -/
theorem lemmaC3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} (hfail : failsOn3 (dec3 S Z) E) :
    Relation.ReflTransGen (S.gadj3 Z ny E) (.inr (.inl false)) (.inr (.inl true)) := by
  by_contra hno
  let R : GNode3 T w h → Prop := fun x => Relation.ReflTransGen (S.gadj3 Z ny E) (.inr (.inl false)) x
  have hstep : ∀ x y, R x → S.gadj3 Z ny E x y → R y := fun x y hx hxy => hx.tail hxy
  have hR0 : R (.inr (.inl false)) := .refl
  let Q : Set (PVert3 T w h) := {v | R (.inl v)}
  have hQclosed : ∀ (f : PEdge3 T w h) (u v : PVert3 T w h), f.ends = {u, v} → u ≠ v → S.ctop3 Z E f ≠ 0 →
      u ∈ Q → v ∈ Q :=
    fun f u v hf huv hX hu => hstep _ _ hu (Or.inl ⟨f, hf, huv, hX⟩)
  have hbotQ : ∀ t x, S.ctop3 Z E (.bot t x) ≠ 0 → ((t, x, 0) : PVert3 T w h) ∈ Q :=
    fun t x hx => hstep _ _ hR0 (Or.inr ⟨t, x, rfl, hx⟩)
  have htopQ : ∀ t x, S.ctop3 Z E (.top t x) ≠ 0 → ((t, x, Fin.last h) : PVert3 T w h) ∉ Q :=
    fun t x hx hQx => hno (hstep _ _ hQx (Or.inl ⟨t, x, rfl, hx⟩))
  have hfamb1 : ∀ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E),
      pcls3 (S.Yfam3 Z E Fm) ≠ 0 → R (.inr (.inr Fm)) :=
    fun Fm hFm hc => hstep _ _ hR0 (Or.inr ⟨hFm, hc⟩)
  have hfamb2 : ∀ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E), R (.inr (.inr Fm)) →
      pclsT3 (S.Yfam3 Z E Fm) = 0 :=
    fun Fm hFm hRF => by
      by_contra hc
      exact hno (hstep _ _ hRF (Or.inl ⟨hFm, hc⟩))
  have hcheckfam : ∀ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E), ∀ u : PVert3 T w h,
      blockOf3 u ∈ Fm → S.om3 E u ≠ 0 → (u ∈ Q ↔ R (.inr (.inr Fm))) :=
    fun Fm hFm u hu hom => ⟨fun hq => hstep _ _ hq (Or.inl ⟨hFm, hu, hom⟩),
      fun hq => hstep _ _ hq (Or.inr ⟨hFm, hu, hom⟩)⟩
  -- the odd checks of `Ω` in `Q`, counted through `C_top`
  have hA1 : ∑ v, (if v ∈ Q then S.om3 E v else 0) = pcls3 (S.ctop3 Z E) := by
    have hh := sum_psyn3_restrict (S.ctop3 Z E) Q hQclosed
    rw [S.psyn3_ctop3] at hh
    rw [hh, pcls3]
    have hb : ∀ t x, (if ((t, x, 0) : PVert3 T w h) ∈ Q then S.ctop3 Z E (.bot t x) else 0) =
        S.ctop3 Z E (.bot t x) := fun t x => by
      by_cases hx : S.ctop3 Z E (.bot t x) = 0
      · rw [hx]
        simp
      · rw [ite_eq_left (hbotQ t x hx)]
    have ht : ∀ t x, (if ((t, x, Fin.last h) : PVert3 T w h) ∈ Q then S.ctop3 Z E (.top t x) else 0) = 0 :=
      fun t x => by
        by_cases hx : S.ctop3 Z E (.top t x) = 0
        · rw [hx]
          simp
        · rw [ite_eq_right (htopQ t x hx)]
    simp only [hb, ht, Finset.sum_const_zero, add_zero]
  -- the odd checks of `Ω` in `Q`, counted through the families
  have hpt : ∀ v, (if v ∈ Q then S.om3 E v else 0) =
      ∑ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E),
        (if R (.inr (.inr Fm)) then restrict3 Fm (S.om3 E) v else 0) := by
    intro v
    by_cases hov : S.om3 E v = 0
    · rw [hov]
      simp [restrict3, hov]
    · have hb := S.bad_of_om3 (ny := ny) hov
      set Fm0 := famF (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (blockOf3 v)
      have hFm0 : Fm0 ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) := famF_mem_families3 hb
      have hv0 : blockOf3 v ∈ Fm0 := self_mem_famF hb
      have hiff := hcheckfam Fm0 hFm0 v hv0 hov
      simp only [restrict3, ← ite_and]
      by_cases hR : R (.inr (.inr Fm0))
      · rw [ite_eq_left (hiff.2 hR), sum_ite_unique]
        exact ⟨Fm0, ⟨hFm0, hR, hv0⟩, fun Fm ⟨hFm, _, hvF⟩ => families3_eq_of_mem hFm hFm0 hvF hv0⟩
      · rw [ite_eq_right (fun hq => hR (hiff.1 hq))]
        refine (Finset.sum_eq_zero fun Fm hFm => ?_).symm
        rw [ite_eq_right]
        rintro ⟨hRF, hvF⟩
        exact hR (families3_eq_of_mem hFm hFm0 hvF hv0 ▸ hRF)
  have hA2 : ∑ v, (if v ∈ Q then S.om3 E v else 0) =
      ∑ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E), pcls3 (S.Yfam3 Z E Fm) := by
    rw [Finset.sum_congr rfl fun v _ => hpt v, Finset.sum_comm]
    refine Finset.sum_congr rfl fun Fm hFm => ?_
    by_cases hR : R (.inr (.inr Fm))
    · simp only [hR, ↓reduceIte]
      rw [show restrict3 Fm (S.om3 E) = psyn3 (S.Yfam3 Z E Fm) from (S.psyn3_Yfam3 Z hFm).symm, sum_psyn3_cls,
        hfamb2 Fm hFm hR, add_zero]
    · simp only [hR, ↓reduceIte, Finset.sum_const_zero]
      by_contra hc
      exact hR (hfamb1 Fm hFm (Ne.symm hc))
  -- then the class of `E + C` would vanish
  apply hfail
  refine ⟨dec3_valid S Z (psyn3 E), ?_⟩
  have hdec := S.pcls3_decomp Z (ny := ny) E
  have hctop : pcls3 (Z.solve Set.univ (omega3 (residD3 S (psyn3 E)))) =
      ∑ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E), pcls3 (S.Yfam3 Z E Fm) := by
    show pcls3 (S.ctop3 Z E) = _
    rw [← hA1, hA2]
  rw [hdec, hctop, CharTwo.add_self_eq_zero]

end Stage13

end QECD1
