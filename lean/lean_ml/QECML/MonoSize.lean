import QECML.Simulation

/-!
# Monotonicity of the ML failure probability in the code size

For fixed `q`, `P_ML(fail; W, H)` is non-increasing in `H` and
non-decreasing in `W` (`W = w + 1` columns, `H = h + 1` rows; rough top and bottom, smooth left and right).

* `H → H + 1` (`pMLPlanar_succ_h`): restrict the error of the code with `h + 2` rows to the rows `0..h`, reading the
  vertical edges between rows `h` and `h + 1` as the top half-edges of the smaller code. The restriction is i.i.d.
  Bernoulli(`q`), has the same class (parity at `b₁`), and its syndrome is the big syndrome on rows `0..h`.
* `W → W + 1` (`pMLPlanar_succ_w`): a randomized decoder of the code with `w + 1` columns draws fresh errors on the
  new column (its vertical edges, the joining horizontal edges and its two half-edges), computes the syndrome of the
  code with `w + 2` columns, decodes it by ML and corrects the class by the new `b₁` half-edge.

Both are instances of the simulation lemma `pML_le_of_sim`.
-/

open Finset

namespace QECML

/-- Splitting a sum over configurations along an equivalence `ι ≃ ι₁ ⊕ ι₂` of the index set. -/
theorem sum_bernProd_split {ι ι₁ ι₂ : Type*} [Fintype ι] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι]
    [DecidableEq ι₁] [DecidableEq ι₂] (σ : ι ≃ ι₁ ⊕ ι₂) (q : ℝ)
    (G : (ι₁ → ZMod 2) → (ι₂ → ZMod 2) → ℝ) :
    ∑ e : ι → ZMod 2, bernProd q e * G (fun i => e (σ.symm (.inl i))) (fun j => e (σ.symm (.inr j))) =
      ∑ a : ι₁ → ZMod 2, ∑ b : ι₂ → ZMod 2, bernProd q a * bernProd q b * G a b := by
  let Φ : (ι → ZMod 2) ≃ (ι₁ → ZMod 2) × (ι₂ → ZMod 2) :=
    (Equiv.arrowCongr σ (Equiv.refl (ZMod 2))).trans (Equiv.sumArrowEquivProdArrow ι₁ ι₂ (ZMod 2))
  have hΦ : ∀ e, Φ e = ((fun i => e (σ.symm (.inl i))), (fun j => e (σ.symm (.inr j)))) := fun e => rfl
  rw [← Fintype.sum_prod_type' (fun a b => bernProd q a * bernProd q b * G a b)]
  refine Fintype.sum_equiv Φ _ _ (fun e => ?_)
  rw [hΦ, bernProd_split σ q e]

/-! ## Endpoints of the planar edges -/

section Ends

variable {w h : ℕ}

theorem ends_hor (x : Fin w) (y : Fin (h + 1)) :
    (PEdge.hor x y : PEdge w h).ends = {(x.castSucc, y), (x.succ, y)} := rfl
theorem ends_ver (x : Fin (w + 1)) (y : Fin h) :
    (PEdge.ver x y : PEdge w h).ends = {(x, y.castSucc), (x, y.succ)} := rfl
theorem ends_bot (x : Fin (w + 1)) : (PEdge.bot x : PEdge w h).ends = {(x, 0)} := rfl
theorem ends_top (x : Fin (w + 1)) : (PEdge.top x : PEdge w h).ends = {(x, Fin.last h)} := rfl

end Ends

/-- Turns an incidence statement about planar edges into linear arithmetic on the coordinates. -/
macro "incidence_simp" : tactic =>
  `(tactic| simp only [ends_hor, ends_ver, ends_bot, ends_top, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero, not_or, not_and])

/-! ## Restriction: `h + 1` rows to `h` rows -/

section Restrict

variable {w h : ℕ}

/-- Edges of the code with `h + 2` rows that the code with `h + 1` rows does not see: the horizontal edges of the
new top row and its half-edges to `b₂`. -/
abbrev XH (w : ℕ) := Fin w ⊕ Fin (w + 1)

/-- The edges of the code with `h + 2` rows as the edges of the code with `h + 1` rows plus the extra edges. The
vertical edge `(x,h)–(x,h+1)` plays the role of the small code's top half-edge at `(x,h)`. -/
def σH : PEdge w (h + 1) ≃ PEdge w h ⊕ XH w where
  toFun
    | .hor x y => Fin.lastCases (motive := fun _ => PEdge w h ⊕ XH w) (.inr (.inl x))
        (fun y' => .inl (.hor x y')) y
    | .ver x y => Fin.lastCases (motive := fun _ => PEdge w h ⊕ XH w) (.inl (.top x))
        (fun y' => .inl (.ver x y')) y
    | .bot x => .inl (.bot x)
    | .top x => .inr (.inr x)
  invFun
    | .inl (.hor x y) => .hor x y.castSucc
    | .inl (.ver x y) => .ver x y.castSucc
    | .inl (.bot x) => .bot x
    | .inl (.top x) => .ver x (Fin.last h)
    | .inr (.inl x) => .hor x (Fin.last (h + 1))
    | .inr (.inr x) => .top x
  left_inv e := by
    rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x
    · induction y using Fin.lastCases with
      | last => simp
      | cast y' => simp
    · induction y using Fin.lastCases with
      | last => simp
      | cast y' => simp
    · rfl
    · rfl
  right_inv s := by
    rcases s with (⟨x, y⟩ | ⟨x, y⟩ | x | x) | (x | x) <;> simp

theorem σH_symm_inl_hor (x : Fin w) (y : Fin (h + 1)) :
    (σH (h := h)).symm (.inl (.hor x y)) = .hor x y.castSucc := rfl
theorem σH_symm_inl_ver (x : Fin (w + 1)) (y : Fin h) :
    (σH (h := h)).symm (.inl (.ver x y)) = .ver x y.castSucc := rfl
theorem σH_symm_inl_bot (x : Fin (w + 1)) : (σH (h := h)).symm (.inl (.bot x)) = .bot x := rfl
theorem σH_symm_inl_top (x : Fin (w + 1)) : (σH (h := h)).symm (.inl (.top x)) = .ver x (Fin.last h) := rfl
theorem σH_symm_inr_inl (x : Fin w) : (σH (h := h)).symm (.inr (.inl x)) = .hor x (Fin.last (h + 1)) := rfl
theorem σH_symm_inr_inr (x : Fin (w + 1)) : (σH (h := h)).symm (.inr (.inr x)) = .top x := rfl

/-- Incidence at the rows `0..h`: the lifted edge of a small-code edge `f` meets the check `(x, y)` (with
`y ≤ h`) iff `f` does. -/
theorem mem_ends_σH_inl (f : PEdge w h) (v : PVert w h) :
    ((v.1, v.2.castSucc) : PVert w (h + 1)) ∈ (σH.symm (.inl f)).ends ↔ v ∈ f.ends := by
  obtain ⟨vx, vy⟩ := v
  rcases f with ⟨x, y⟩ | ⟨x, y⟩ | x | x <;>
  · simp only [σH_symm_inl_hor, σH_symm_inl_ver, σH_symm_inl_bot, σH_symm_inl_top]
    incidence_simp <;> omega

/-- The extra edges meet no check of the rows `0..h`. -/
theorem not_mem_ends_σH_inr (j : XH w) (v : PVert w h) :
    ((v.1, v.2.castSucc) : PVert w (h + 1)) ∉ (σH.symm (.inr j)).ends := by
  obtain ⟨vx, vy⟩ := v
  rcases j with x | x <;>
  · simp only [σH_symm_inr_inl, σH_symm_inr_inr]
    incidence_simp
    omega

end Restrict

/-! ## Extension: `w + 1` columns to `w + 2` columns -/

section Extend

variable {w h : ℕ}

/-- Edges of the code with `w + 2` columns outside the code with `w + 1` columns: the joining horizontal edges
`(w,y)–(w+1,y)`, the vertical edges of the new column, and its half-edges to `b₁` (`false`) and `b₂` (`true`). -/
abbrev XW (h : ℕ) := Fin (h + 1) ⊕ Fin h ⊕ Bool

/-- The edges of the code with `w + 2` columns as the edges of the code with `w + 1` columns plus the new edges. -/
def σW : PEdge (w + 1) h ≃ PEdge w h ⊕ XW h where
  toFun
    | .hor x y => Fin.lastCases (motive := fun _ => PEdge w h ⊕ XW h) (.inr (.inl y))
        (fun x' => .inl (.hor x' y)) x
    | .ver x y => Fin.lastCases (motive := fun _ => PEdge w h ⊕ XW h) (.inr (.inr (.inl y)))
        (fun x' => .inl (.ver x' y)) x
    | .bot x => Fin.lastCases (motive := fun _ => PEdge w h ⊕ XW h) (.inr (.inr (.inr false)))
        (fun x' => .inl (.bot x')) x
    | .top x => Fin.lastCases (motive := fun _ => PEdge w h ⊕ XW h) (.inr (.inr (.inr true)))
        (fun x' => .inl (.top x')) x
  invFun
    | .inl (.hor x y) => .hor x.castSucc y
    | .inl (.ver x y) => .ver x.castSucc y
    | .inl (.bot x) => .bot x.castSucc
    | .inl (.top x) => .top x.castSucc
    | .inr (.inl y) => .hor (Fin.last w) y
    | .inr (.inr (.inl y)) => .ver (Fin.last (w + 1)) y
    | .inr (.inr (.inr false)) => .bot (Fin.last (w + 1))
    | .inr (.inr (.inr true)) => .top (Fin.last (w + 1))
  left_inv e := by
    rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x <;>
    · induction x using Fin.lastCases with
      | last => simp
      | cast x' => simp
  right_inv s := by
    rcases s with (⟨x, y⟩ | ⟨x, y⟩ | x | x) | (y | y | b)
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · cases b <;> simp

theorem σW_symm_inl_hor (x : Fin w) (y : Fin (h + 1)) :
    (σW (w := w) (h := h)).symm (.inl (.hor x y)) = .hor x.castSucc y := rfl
theorem σW_symm_inl_ver (x : Fin (w + 1)) (y : Fin h) :
    (σW (w := w) (h := h)).symm (.inl (.ver x y)) = .ver x.castSucc y := rfl
theorem σW_symm_inl_bot (x : Fin (w + 1)) : (σW (w := w) (h := h)).symm (.inl (.bot x)) = .bot x.castSucc :=
  rfl
theorem σW_symm_inl_top (x : Fin (w + 1)) : (σW (w := w) (h := h)).symm (.inl (.top x)) = .top x.castSucc :=
  rfl

/-- Incidence at the old columns: the embedded edge of `f` meets `(x, y)` (with `x ≤ w`) iff `f` does. -/
theorem mem_ends_σW_inl (f : PEdge w h) (v : PVert w h) :
    ((v.1.castSucc, v.2) : PVert (w + 1) h) ∈ (σW.symm (.inl f)).ends ↔ v ∈ f.ends := by
  obtain ⟨vx, vy⟩ := v
  rcases f with ⟨x, y⟩ | ⟨x, y⟩ | x | x <;>
  · simp only [σW_symm_inl_hor, σW_symm_inl_ver, σW_symm_inl_bot, σW_symm_inl_top]
    incidence_simp

/-- The embedded old edges meet no check of the new column. -/
theorem not_mem_ends_σW_inl_last (f : PEdge w h) (y : Fin (h + 1)) :
    ((Fin.last (w + 1), y) : PVert (w + 1) h) ∉ (σW.symm (.inl f)).ends := by
  rcases f with ⟨x, y'⟩ | ⟨x, y'⟩ | x | x <;>
  · simp only [σW_symm_inl_hor, σW_symm_inl_ver, σW_symm_inl_bot, σW_symm_inl_top]
    incidence_simp
    omega

end Extend

/-! ## Syndromes and classes under restriction and extension -/

section Compat

variable {w h : ℕ}

theorem psyn_apply (e : PEdge w h → ZMod 2) (v : PVert w h) :
    psyn w h e v = ∑ f, (if v ∈ f.ends then 1 else 0) * e f := rfl

theorem pcls_apply (e : PEdge w h → ZMod 2) : pcls w h e = ∑ x, e (.bot x) := rfl

/-- Restriction of a configuration of the code with `h + 2` rows to the code with `h + 1` rows. -/
def restrictH (e : PEdge w (h + 1) → ZMod 2) : PEdge w h → ZMod 2 := fun f => e (σH.symm (.inl f))

/-- The syndrome of the restriction is the big syndrome on the rows `0..h`. -/
theorem psyn_restrictH (e : PEdge w (h + 1) → ZMod 2) (v : PVert w h) :
    psyn w h (restrictH e) v = psyn w (h + 1) e (v.1, v.2.castSucc) := by
  rw [psyn_apply, psyn_apply, ← Equiv.sum_comp σH.symm, Fintype.sum_sum_type]
  have h2 : ∀ j : XH w, (if ((v.1, v.2.castSucc) : PVert w (h + 1)) ∈ (σH.symm (.inr j)).ends then
      (1 : ZMod 2) else 0) * e (σH.symm (.inr j)) = 0 := fun j => by
    simp [not_mem_ends_σH_inr j v]
  simp only [h2, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [mem_ends_σH_inl f v, restrictH]

/-- The restriction has the same class (the `b₁` half-edges are unchanged). -/
theorem pcls_restrictH (e : PEdge w (h + 1) → ZMod 2) : pcls w h (restrictH e) = pcls w (h + 1) e := rfl

/-- Gluing a configuration of the code with `w + 1` columns and one of the new edges. -/
def glueW (a : PEdge w h → ZMod 2) (b : XW h → ZMod 2) : PEdge (w + 1) h → ZMod 2 :=
  fun g => Sum.elim a b (σW g)

theorem glueW_split (e : PEdge (w + 1) h → ZMod 2) :
    glueW (fun f => e (σW.symm (.inl f))) (fun j => e (σW.symm (.inr j))) = e := by
  funext g
  simp only [glueW]
  rcases hg : σW g with f | j
  · rw [Sum.elim_inl, ← hg, Equiv.symm_apply_apply]
  · rw [Sum.elim_inr, ← hg, Equiv.symm_apply_apply]

/-- Syndrome contribution of the new edges. -/
def extraSynW (b : XW h → ZMod 2) (v : PVert (w + 1) h) : ZMod 2 :=
  ∑ j, (if v ∈ (σW.symm (.inr j)).ends then 1 else 0) * b j

/-- The syndrome of the glued configuration, as a function of the old syndrome and the new edges. -/
def gW (s : PVert w h → ZMod 2) (b : XW h → ZMod 2) (v : PVert (w + 1) h) : ZMod 2 :=
  Fin.lastCases (motive := fun _ => ZMod 2) 0 (fun x' => s (x', v.2)) v.1 + extraSynW b v

theorem psyn_glueW (a : PEdge w h → ZMod 2) (b : XW h → ZMod 2) :
    psyn (w + 1) h (glueW a b) = gW (psyn w h a) b := by
  funext v
  rw [psyn_apply, ← Equiv.sum_comp σW.symm, Fintype.sum_sum_type, gW, extraSynW]
  have hl : ∀ f, glueW a b (σW.symm (.inl f)) = a f := fun f => by
    simp only [glueW, Equiv.apply_symm_apply, Sum.elim_inl]
  have hr : ∀ j, glueW a b (σW.symm (.inr j)) = b j := fun j => by
    simp only [glueW, Equiv.apply_symm_apply, Sum.elim_inr]
  simp only [hl, hr]
  congr 1
  obtain ⟨vx, vy⟩ := v
  induction vx using Fin.lastCases with
  | last =>
    rw [Fin.lastCases_last]
    refine Finset.sum_eq_zero fun f _ => ?_
    simp [not_mem_ends_σW_inl_last f vy]
  | cast x' =>
    rw [Fin.lastCases_castSucc, psyn_apply]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [mem_ends_σW_inl f (x', vy)]

theorem σW_bot_castSucc (x : Fin (w + 1)) : (σW (h := h)) (.bot x.castSucc) = .inl (.bot x) := by
  show Fin.lastCases (motive := fun _ => PEdge w h ⊕ XW h) (.inr (.inr (.inr false)))
    (fun x' => .inl (.bot x')) x.castSucc = _
  rw [Fin.lastCases_castSucc]

theorem σW_bot_last : (σW (w := w) (h := h)) (.bot (Fin.last (w + 1))) = .inr (.inr (.inr false)) := by
  show Fin.lastCases (motive := fun _ => PEdge w h ⊕ XW h) (.inr (.inr (.inr false)))
    (fun x' => .inl (.bot x')) (Fin.last (w + 1)) = _
  rw [Fin.lastCases_last]

/-- The class of the glued configuration: old class plus the new `b₁` half-edge. -/
theorem pcls_glueW (a : PEdge w h → ZMod 2) (b : XW h → ZMod 2) :
    pcls (w + 1) h (glueW a b) = pcls w h a + b (.inr (.inr false)) := by
  rw [pcls_apply, pcls_apply, Fin.sum_univ_castSucc]
  simp only [glueW, σW_bot_castSucc, σW_bot_last, Sum.elim_inl, Sum.elim_inr]

end Compat

/-! ## Proposition M -/

/-- Proposition M, `H → H + 1`: adding a row of checks at a rough side cannot increase the ML failure probability. -/
theorem pMLPlanar_succ_h (w h : ℕ) {q : ℝ} :
    pMLPlanar w (h + 1) q ≤ pMLPlanar w h q := by
  unfold pMLPlanar
  refine pML_le_of_sim (bernProd q) (psyn w (h + 1)) (pcls w (h + 1)) (bernProd q) (psyn w h) (pcls w h)
    (fun _ : Unit => (1 : ℝ)) (fun _ => zero_le_one) (by simp) (fun e _ => restrictH e) ?_
    (fun s _ v => s (v.1, v.2.castSucc)) ?_ (fun _ => 0) ?_
  · intro F
    have hs := sum_bernProd_split (σH (w := w) (h := h)) q (fun a _ => F a)
    simp only [Fintype.sum_unique, mul_one]
    rw [show (∑ e, bernProd q e * F (restrictH e)) =
        ∑ e : PEdge w (h + 1) → ZMod 2, bernProd q e * F (fun i => e (σH.symm (.inl i))) from rfl, hs]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_bernProd, mul_one]
  · intro e _
    funext v
    exact psyn_restrictH e v
  · intro e _
    exact (pcls_restrictH e).trans (add_zero _).symm

/-- Proposition M, `W → W + 1`: adding a column of checks at a smooth side cannot decrease the ML failure
probability (for `0 ≤ q ≤ 1`, so that the fresh errors of the new column have a law). -/
theorem pMLPlanar_succ_w (w h : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    pMLPlanar w h q ≤ pMLPlanar (w + 1) h q := by
  unfold pMLPlanar
  refine pML_le_of_sim (bernProd q) (psyn w h) (pcls w h) (bernProd q) (psyn (w + 1) h) (pcls (w + 1) h)
    (bernProd q) (bernProd_nonneg hq0 hq1) (sum_bernProd q) (fun a b => glueW a b) ?_
    (fun s b => gW s b) ?_ (fun b => b (.inr (.inr false))) ?_
  · intro F
    have hs := sum_bernProd_split (σW (w := w) (h := h)) q (fun a b => F (glueW a b))
    simp only [glueW_split] at hs
    rw [← hs]
  · intro a b
    exact psyn_glueW a b
  · intro a b
    exact pcls_glueW a b

theorem pMLPlanar_antitone_h (w : ℕ) (q : ℝ) : Antitone fun h => pMLPlanar w h q :=
  antitone_nat_of_succ_le fun h => pMLPlanar_succ_h w h

theorem pMLPlanar_monotone_w (h : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Monotone fun w => pMLPlanar w h q :=
  monotone_nat_of_le_succ fun w => pMLPlanar_succ_w w h hq0 hq1

/-- Rounding the code size: widening (`w ≤ w'`) and lowering (`h' ≤ h`) can only increase the ML failure
probability. Used with `W` rounded up and `H` rounded down to multiples of the block side. -/
theorem pMLPlanar_mono_size {w w' h h' : ℕ} (hw : w ≤ w') (hh : h' ≤ h) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    pMLPlanar w h q ≤ pMLPlanar w' h' q :=
  (pMLPlanar_antitone_h w q hh).trans (pMLPlanar_monotone_w h' hq0 hq1 hw)

end QECML
