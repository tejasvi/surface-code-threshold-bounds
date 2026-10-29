import QECD1.MLGen
import QECD1.LemmaC3

/-!
# Monotonicity: the ML failure probability of the 3D code is monotone in `q`, `W`, `H` and `T`

The 3D (phenomenological) analogue of the 2D `MonoQ` and `MonoSize`. `pML3 T w h q` is the ML failure probability
of the code with checks `(t, x, y)`, `t ≤ T`, `x ≤ w`, `y ≤ h` (`T + 1` detector layers, `W = w + 1` columns,
`H = h + 1` rows), every edge flipped independently with probability `q`, syndrome `psyn3`, class `pcls3` (the
parity at `b₁` over all layers).

* `pML3_mono_q`: non-decreasing in `q` on `[0, 1/2]`.
* `pML3_succ_h` (`H → H + 1`): restrict the error of the code with `h + 2` rows to the rows `0..h`, in every layer;
  the vertical edges between the rows `h` and `h + 1` play the small code's top half-edges (`sigH3`). The new row's
  horizontal edges, time edges and half-edges are dropped.
* `pML3_succ_w` (`W → W + 1`): a decoder of the code with `w + 1` columns draws fresh errors on the new column (its
  vertical, time and joining horizontal edges and its half-edges, in every layer), forms the big syndrome, decodes
  it by ML and corrects the class by the new `b₁` half-edges (`sigW3`).
* `pML3_succ_t` (`T → T + 1`): the same with a new layer `T + 1` (its horizontal and vertical edges and half-edges)
  and the time edges between the layers `T` and `T + 1` (`sigT3`). The code with `T` noisy rounds is the code with
  `T + 1` noisy rounds restricted to the layers `0..T`, so the decoder of the smaller code simulates the bigger one.
* `pML3_mono_size`: for `T ≤ T'`, `w ≤ w'`, `h' ≤ h`, `pML3 T w h q ≤ pML3 T' w' h' q`.

The three steps are instances of two generic statements for a splitting `σ` of the edges of one code into the
edges of another plus extra edges, with a map `ι` of the checks: restriction (`pML3_le_of_slice`) and extension
(`pML3_le_of_glue`), both from the simulation lemma `pML_le_of_sim`.
-/

open Finset

namespace QECD1

/-- The ML failure probability of the 3D code with `T + 1` layers, `w + 1` columns and `h + 1` rows at rate `q`. -/
noncomputable def pML3 (T w h : ℕ) (q : ℝ) : ℝ :=
  pML (bernProd q) (psyn3 (T := T) (w := w) (h := h)) (pcls3 (T := T) (w := w) (h := h))

/-- The syndrome map as an additive map. -/
def psyn3Hom (T w h : ℕ) : (PEdge3 T w h → ZMod 2) →+ (PVert3 T w h → ZMod 2) where
  toFun := psyn3
  map_zero' := psyn3_zero
  map_add' := psyn3_add

/-- The class map as an additive map. -/
noncomputable def pcls3Hom (T w h : ℕ) : (PEdge3 T w h → ZMod 2) →+ ZMod 2 where
  toFun := pcls3
  map_zero' := pcls3_zero
  map_add' := pcls3_add

/-- **Monotonicity in `q` for the 3D code**: for `q ≤ q' ≤ 1/2`, `pML3 T w h q ≤ pML3 T w h q'`. -/
theorem pML3_mono_q (T w h : ℕ) {q q' : ℝ} (hqq' : q ≤ q') (hq' : q' ≤ 1 / 2) :
    pML3 T w h q ≤ pML3 T w h q' :=
  pML_mono_q (psyn3Hom T w h) (pcls3Hom T w h) hqq' hq'

/-! ## Endpoints of the edges -/

section Ends

variable {T w h : ℕ}

theorem ends3_hor (t : Fin (T + 1)) (x : Fin w) (y : Fin (h + 1)) :
    (PEdge3.hor t x y : PEdge3 T w h).ends = {(t, x.castSucc, y), (t, x.succ, y)} := rfl
theorem ends3_ver (t : Fin (T + 1)) (x : Fin (w + 1)) (y : Fin h) :
    (PEdge3.ver t x y : PEdge3 T w h).ends = {(t, x, y.castSucc), (t, x, y.succ)} := rfl
theorem ends3_time (t : Fin T) (x : Fin (w + 1)) (y : Fin (h + 1)) :
    (PEdge3.time t x y : PEdge3 T w h).ends = {(t.castSucc, x, y), (t.succ, x, y)} := rfl
theorem ends3_bot (t : Fin (T + 1)) (x : Fin (w + 1)) : (PEdge3.bot t x : PEdge3 T w h).ends = {(t, x, 0)} := rfl
theorem ends3_top (t : Fin (T + 1)) (x : Fin (w + 1)) :
    (PEdge3.top t x : PEdge3 T w h).ends = {(t, x, Fin.last h)} := rfl

end Ends

/-- Turns an incidence statement about 3D edges into linear arithmetic on the coordinates. -/
macro "incidence3_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [ends3_hor, ends3_ver, ends3_time, ends3_bot, ends3_top, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero,
    not_or, not_and] $[$loc]?)

/-! ## Restriction and extension along a splitting of the edges -/

section Glue

variable {T w h T' w' h' : ℕ} {X : Type} [Fintype X]

theorem psyn3_eq_sum (Y : PEdge3 T w h → ZMod 2) (v : PVert3 T w h) :
    psyn3 Y v = ∑ e, if v ∈ e.ends then Y e else 0 := by
  rw [psyn3, Finset.sum_filter]

/-- The part of a configuration of the code `(T', w', h')` on the edges of the code `(T, w, h)`, along `σ`. -/
def sliceE (σ : PEdge3 T' w' h' ≃ PEdge3 T w h ⊕ X) (e : PEdge3 T' w' h' → ZMod 2) : PEdge3 T w h → ZMod 2 :=
  fun f => e (σ.symm (.inl f))

/-- The syndrome of a slice is the big syndrome read through `ι`, if `σ` preserves the incidence at the checks
`ι v` and the extra edges meet no check `ι v`. -/
theorem psyn3_sliceE (σ : PEdge3 T' w' h' ≃ PEdge3 T w h ⊕ X) (ι : PVert3 T w h → PVert3 T' w' h')
    (hin : ∀ f v, ι v ∈ (σ.symm (.inl f)).ends ↔ v ∈ f.ends) (hx : ∀ j v, ι v ∉ (σ.symm (.inr j)).ends)
    (e : PEdge3 T' w' h' → ZMod 2) (v : PVert3 T w h) : psyn3 (sliceE σ e) v = psyn3 e (ι v) := by
  rw [psyn3_eq_sum, psyn3_eq_sum, ← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]
  simp only [hx, ite_false, Finset.sum_const_zero, add_zero, hin, sliceE]

/-- Gluing a configuration of the code `(T, w, h)` and one of the extra edges, along `σ`. -/
def glueE (σ : PEdge3 T' w' h' ≃ PEdge3 T w h ⊕ X) (a : PEdge3 T w h → ZMod 2) (b : X → ZMod 2) :
    PEdge3 T' w' h' → ZMod 2 :=
  fun g => Sum.elim a b (σ g)

omit [Fintype X] in
theorem glueE_split (σ : PEdge3 T' w' h' ≃ PEdge3 T w h ⊕ X) (e : PEdge3 T' w' h' → ZMod 2) :
    glueE σ (fun f => e (σ.symm (.inl f))) (fun j => e (σ.symm (.inr j))) = e := by
  funext g
  simp only [glueE]
  rcases hg : σ g with f | j
  · rw [Sum.elim_inl, ← hg, Equiv.symm_apply_apply]
  · rw [Sum.elim_inr, ← hg, Equiv.symm_apply_apply]

/-- The syndrome of a glued configuration, as a function of the small syndrome `s` and the extra edges `b`. -/
def glueSyn (σ : PEdge3 T' w' h' ≃ PEdge3 T w h ⊕ X) (ι : PVert3 T w h → PVert3 T' w' h')
    (s : PVert3 T w h → ZMod 2) (b : X → ZMod 2) (v' : PVert3 T' w' h') : ZMod 2 :=
  (∑ v ∈ Finset.univ.filter (fun v => ι v = v'), s v) + ∑ j, if v' ∈ (σ.symm (.inr j)).ends then b j else 0

/-- The syndrome of a glued configuration, if `ι` is injective, `σ` preserves the incidence at the checks `ι v`,
and the ends of the small code's edges are checks `ι v`. -/
theorem psyn3_glueE (σ : PEdge3 T' w' h' ≃ PEdge3 T w h ⊕ X) (ι : PVert3 T w h → PVert3 T' w' h')
    (hι : Function.Injective ι) (hin : ∀ f v, ι v ∈ (σ.symm (.inl f)).ends ↔ v ∈ f.ends)
    (hout : ∀ f v', v' ∈ (σ.symm (.inl f)).ends → ∃ v, ι v = v') (a : PEdge3 T w h → ZMod 2) (b : X → ZMod 2) :
    psyn3 (glueE σ a b) = glueSyn σ ι (psyn3 a) b := by
  funext v'
  rw [psyn3_eq_sum, ← Equiv.sum_comp σ.symm, Fintype.sum_sum_type, glueSyn]
  have hl : ∀ f, glueE σ a b (σ.symm (.inl f)) = a f := fun f => by
    simp only [glueE, Equiv.apply_symm_apply, Sum.elim_inl]
  have hr : ∀ j, glueE σ a b (σ.symm (.inr j)) = b j := fun j => by
    simp only [glueE, Equiv.apply_symm_apply, Sum.elim_inr]
  simp only [hl, hr]
  congr 1
  by_cases hv : ∃ v, ι v = v'
  · obtain ⟨v, rfl⟩ := hv
    have hf : Finset.univ.filter (fun u => ι u = ι v) = {v} := by
      ext u
      simp [hι.eq_iff]
    rw [hf, Finset.sum_singleton, psyn3_eq_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [hin]
  · have hf : Finset.univ.filter (fun u => ι u = v') = ∅ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun hu => hv ⟨u, hu⟩
    rw [hf, Finset.sum_empty]
    exact Finset.sum_eq_zero fun f _ => ite_eq_right_iff.2 fun hmem => absurd (hout f v' hmem) hv

variable [DecidableEq X]

/-- **Restriction**: if the code `(T', w', h')` splits into the code `(T, w, h)` and extra edges, with the small
syndrome read through `ι` and the same class, then `pML3 T' w' h' q ≤ pML3 T w h q`. -/
theorem pML3_le_of_slice (σ : PEdge3 T' w' h' ≃ PEdge3 T w h ⊕ X) (ι : PVert3 T w h → PVert3 T' w' h')
    (hin : ∀ f v, ι v ∈ (σ.symm (.inl f)).ends ↔ v ∈ f.ends) (hx : ∀ j v, ι v ∉ (σ.symm (.inr j)).ends)
    (hcls : ∀ e, pcls3 (sliceE σ e) = pcls3 e) (q : ℝ) : pML3 T' w' h' q ≤ pML3 T w h q := by
  unfold pML3
  refine pML_le_of_sim (bernProd q) psyn3 pcls3 (bernProd q) psyn3 pcls3
    (fun _ : Unit => (1 : ℝ)) (fun _ => zero_le_one) (by simp) (fun e _ => sliceE σ e) ?_
    (fun s _ v => s (ι v)) ?_ (fun _ => 0) ?_
  · intro F
    have hs := sum_bernProd_split σ q (fun a _ => F a)
    simp only [Fintype.sum_unique, mul_one]
    rw [show (∑ e, bernProd q e * F (sliceE σ e)) =
        ∑ e : PEdge3 T' w' h' → ZMod 2, bernProd q e * F (fun i => e (σ.symm (.inl i))) from rfl, hs]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_bernProd, mul_one]
  · intro e _
    funext v
    exact psyn3_sliceE σ ι hin hx e v
  · intro e _
    exact (hcls e).trans (add_zero _).symm

/-- **Extension**: if the code `(T', w', h')` splits into the code `(T, w, h)` and extra edges, with `ι` injective,
the incidence preserved and the class of a glued configuration the small class plus `k` of the extra edges, then
`pML3 T w h q ≤ pML3 T' w' h' q` (for `0 ≤ q ≤ 1`, so that the extra edges have a law). -/
theorem pML3_le_of_glue (σ : PEdge3 T' w' h' ≃ PEdge3 T w h ⊕ X) (ι : PVert3 T w h → PVert3 T' w' h')
    (hι : Function.Injective ι) (hin : ∀ f v, ι v ∈ (σ.symm (.inl f)).ends ↔ v ∈ f.ends)
    (hout : ∀ f v', v' ∈ (σ.symm (.inl f)).ends → ∃ v, ι v = v') (k : (X → ZMod 2) → ZMod 2)
    (hcls : ∀ a b, pcls3 (glueE σ a b) = pcls3 a + k b) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    pML3 T w h q ≤ pML3 T' w' h' q := by
  unfold pML3
  refine pML_le_of_sim (bernProd q) psyn3 pcls3 (bernProd q) psyn3 pcls3
    (bernProd q) (bernProd_nonneg hq0 hq1) (sum_bernProd q) (fun a b => glueE σ a b) ?_
    (fun s b => glueSyn σ ι s b) ?_ k ?_
  · intro F
    have hs := sum_bernProd_split σ q (fun a b => F (glueE σ a b))
    simp only [glueE_split] at hs
    rw [← hs]
  · intro a b
    exact psyn3_glueE σ ι hι hin hout a b
  · intro a b
    exact hcls a b

end Glue

/-! ## `H → H + 1`: restriction to the rows `0..h` -/

section RowH

variable {T w h : ℕ}

/-- Edges of the code with `h + 2` rows that the code with `h + 1` rows does not see: the horizontal edges, the time
edges and the half-edges to `b₂` of the new top row, in every layer. -/
abbrev XH3 (T w : ℕ) := (Fin (T + 1) × Fin w) ⊕ (Fin T × Fin (w + 1)) ⊕ (Fin (T + 1) × Fin (w + 1))

/-- The edges of the code with `h + 2` rows as the edges of the code with `h + 1` rows plus the extra edges. The
vertical edge `(t,x,h)–(t,x,h+1)` plays the role of the small code's top half-edge at `(t,x,h)`. -/
def sigH3 : PEdge3 T w (h + 1) ≃ PEdge3 T w h ⊕ XH3 T w where
  toFun
    | .hor t x y => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XH3 T w) (.inr (.inl (t, x)))
        (fun y' => .inl (.hor t x y')) y
    | .ver t x y => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XH3 T w) (.inl (.top t x))
        (fun y' => .inl (.ver t x y')) y
    | .time t x y => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XH3 T w) (.inr (.inr (.inl (t, x))))
        (fun y' => .inl (.time t x y')) y
    | .bot t x => .inl (.bot t x)
    | .top t x => .inr (.inr (.inr (t, x)))
  invFun
    | .inl (.hor t x y) => .hor t x y.castSucc
    | .inl (.ver t x y) => .ver t x y.castSucc
    | .inl (.time t x y) => .time t x y.castSucc
    | .inl (.bot t x) => .bot t x
    | .inl (.top t x) => .ver t x (Fin.last h)
    | .inr (.inl (t, x)) => .hor t x (Fin.last (h + 1))
    | .inr (.inr (.inl (t, x))) => .time t x (Fin.last (h + 1))
    | .inr (.inr (.inr (t, x))) => .top t x
  left_inv e := by
    rcases e with ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩
    · induction y using Fin.lastCases with
      | last => simp
      | cast y' => simp
    · induction y using Fin.lastCases with
      | last => simp
      | cast y' => simp
    · induction y using Fin.lastCases with
      | last => simp
      | cast y' => simp
    · rfl
    · rfl
  right_inv s := by
    rcases s with (⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩) | (⟨t, x⟩ | ⟨t, x⟩ | ⟨t, x⟩) <;> simp

theorem sigH3_symm_inl_hor (t : Fin (T + 1)) (x : Fin w) (y : Fin (h + 1)) :
    (sigH3 (h := h)).symm (.inl (.hor t x y)) = .hor t x y.castSucc := rfl
theorem sigH3_symm_inl_ver (t : Fin (T + 1)) (x : Fin (w + 1)) (y : Fin h) :
    (sigH3 (h := h)).symm (.inl (.ver t x y)) = .ver t x y.castSucc := rfl
theorem sigH3_symm_inl_time (t : Fin T) (x : Fin (w + 1)) (y : Fin (h + 1)) :
    (sigH3 (h := h)).symm (.inl (.time t x y)) = .time t x y.castSucc := rfl
theorem sigH3_symm_inl_bot (t : Fin (T + 1)) (x : Fin (w + 1)) :
    (sigH3 (h := h)).symm (.inl (.bot t x)) = .bot t x := rfl
theorem sigH3_symm_inl_top (t : Fin (T + 1)) (x : Fin (w + 1)) :
    (sigH3 (h := h)).symm (.inl (.top t x)) = .ver t x (Fin.last h) := rfl
theorem sigH3_symm_inr_hor (t : Fin (T + 1)) (x : Fin w) :
    (sigH3 (h := h)).symm (.inr (.inl (t, x))) = .hor t x (Fin.last (h + 1)) := rfl
theorem sigH3_symm_inr_time (t : Fin T) (x : Fin (w + 1)) :
    (sigH3 (h := h)).symm (.inr (.inr (.inl (t, x)))) = .time t x (Fin.last (h + 1)) := rfl
theorem sigH3_symm_inr_top (t : Fin (T + 1)) (x : Fin (w + 1)) :
    (sigH3 (h := h)).symm (.inr (.inr (.inr (t, x)))) = .top t x := rfl

/-- The checks of the code with `h + 1` rows as the checks of the rows `0..h` of the code with `h + 2` rows. -/
def iotaH3 (v : PVert3 T w h) : PVert3 T w (h + 1) := (v.1, v.2.1, v.2.2.castSucc)

theorem sigH3_in (f : PEdge3 T w h) (v : PVert3 T w h) :
    iotaH3 v ∈ (sigH3.symm (.inl f)).ends ↔ v ∈ f.ends := by
  obtain ⟨vt, vx, vy⟩ := v
  rcases f with ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩ <;>
  · simp only [iotaH3, sigH3_symm_inl_hor, sigH3_symm_inl_ver, sigH3_symm_inl_time, sigH3_symm_inl_bot,
      sigH3_symm_inl_top]
    incidence3_simp <;> omega

theorem sigH3_out (j : XH3 T w) (v : PVert3 T w h) : iotaH3 v ∉ (sigH3.symm (.inr j)).ends := by
  obtain ⟨vt, vx, vy⟩ := v
  rcases j with ⟨t, x⟩ | ⟨t, x⟩ | ⟨t, x⟩ <;>
  · simp only [iotaH3, sigH3_symm_inr_hor, sigH3_symm_inr_time, sigH3_symm_inr_top]
    incidence3_simp
    omega

theorem pcls3_sliceH (e : PEdge3 T w (h + 1) → ZMod 2) : pcls3 (sliceE sigH3 e) = pcls3 e := rfl

/-- **Monotonicity, `H → H + 1`**: adding a row of checks at a rough side, in every layer, cannot increase the
ML failure probability. -/
theorem pML3_succ_h (T w h : ℕ) (q : ℝ) : pML3 T w (h + 1) q ≤ pML3 T w h q :=
  pML3_le_of_slice sigH3 iotaH3 sigH3_in sigH3_out pcls3_sliceH q

end RowH

/-! ## `W → W + 1`: a new column -/

section ColW

variable {T w h : ℕ}

/-- Edges of the code with `w + 2` columns outside the code with `w + 1` columns, in every layer: the joining
horizontal edges `(t,w,y)–(t,w+1,y)`, the vertical and time edges of the new column, and its half-edges to `b₁`
(`false`) and `b₂` (`true`). -/
abbrev XW3 (T h : ℕ) :=
  (Fin (T + 1) × Fin (h + 1)) ⊕ (Fin (T + 1) × Fin h) ⊕ (Fin T × Fin (h + 1)) ⊕ (Fin (T + 1) × Bool)

/-- The edges of the code with `w + 2` columns as the edges of the code with `w + 1` columns plus the new edges. -/
def sigW3 : PEdge3 T (w + 1) h ≃ PEdge3 T w h ⊕ XW3 T h where
  toFun
    | .hor t x y => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XW3 T h) (.inr (.inl (t, y)))
        (fun x' => .inl (.hor t x' y)) x
    | .ver t x y => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XW3 T h) (.inr (.inr (.inl (t, y))))
        (fun x' => .inl (.ver t x' y)) x
    | .time t x y => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XW3 T h) (.inr (.inr (.inr (.inl (t, y)))))
        (fun x' => .inl (.time t x' y)) x
    | .bot t x => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XW3 T h) (.inr (.inr (.inr (.inr (t, false)))))
        (fun x' => .inl (.bot t x')) x
    | .top t x => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XW3 T h) (.inr (.inr (.inr (.inr (t, true)))))
        (fun x' => .inl (.top t x')) x
  invFun
    | .inl (.hor t x y) => .hor t x.castSucc y
    | .inl (.ver t x y) => .ver t x.castSucc y
    | .inl (.time t x y) => .time t x.castSucc y
    | .inl (.bot t x) => .bot t x.castSucc
    | .inl (.top t x) => .top t x.castSucc
    | .inr (.inl (t, y)) => .hor t (Fin.last w) y
    | .inr (.inr (.inl (t, y))) => .ver t (Fin.last (w + 1)) y
    | .inr (.inr (.inr (.inl (t, y)))) => .time t (Fin.last (w + 1)) y
    | .inr (.inr (.inr (.inr (t, false)))) => .bot t (Fin.last (w + 1))
    | .inr (.inr (.inr (.inr (t, true)))) => .top t (Fin.last (w + 1))
  left_inv e := by
    rcases e with ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩ <;>
    · induction x using Fin.lastCases with
      | last => simp
      | cast x' => simp
  right_inv s := by
    rcases s with (⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩) | (⟨t, y⟩ | ⟨t, y⟩ | ⟨t, y⟩ | ⟨t, b⟩)
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · cases b <;> simp

theorem sigW3_symm_inl_hor (t : Fin (T + 1)) (x : Fin w) (y : Fin (h + 1)) :
    (sigW3 (w := w) (h := h)).symm (.inl (.hor t x y)) = .hor t x.castSucc y := rfl
theorem sigW3_symm_inl_ver (t : Fin (T + 1)) (x : Fin (w + 1)) (y : Fin h) :
    (sigW3 (w := w) (h := h)).symm (.inl (.ver t x y)) = .ver t x.castSucc y := rfl
theorem sigW3_symm_inl_time (t : Fin T) (x : Fin (w + 1)) (y : Fin (h + 1)) :
    (sigW3 (w := w) (h := h)).symm (.inl (.time t x y)) = .time t x.castSucc y := rfl
theorem sigW3_symm_inl_bot (t : Fin (T + 1)) (x : Fin (w + 1)) :
    (sigW3 (w := w) (h := h)).symm (.inl (.bot t x)) = .bot t x.castSucc := rfl
theorem sigW3_symm_inl_top (t : Fin (T + 1)) (x : Fin (w + 1)) :
    (sigW3 (w := w) (h := h)).symm (.inl (.top t x)) = .top t x.castSucc := rfl

/-- The checks of the code with `w + 1` columns as the checks of the columns `0..w` of the code with `w + 2`
columns. -/
def iotaW3 (v : PVert3 T w h) : PVert3 T (w + 1) h := (v.1, v.2.1.castSucc, v.2.2)

theorem iotaW3_inj : Function.Injective (iotaW3 (T := T) (w := w) (h := h)) := by
  rintro ⟨t, x, y⟩ ⟨t', x', y'⟩ hv
  simp only [iotaW3, Prod.mk.injEq, Fin.castSucc_inj] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  rfl

theorem sigW3_in (f : PEdge3 T w h) (v : PVert3 T w h) :
    iotaW3 v ∈ (sigW3.symm (.inl f)).ends ↔ v ∈ f.ends := by
  obtain ⟨vt, vx, vy⟩ := v
  rcases f with ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩ <;>
  · simp only [iotaW3, sigW3_symm_inl_hor, sigW3_symm_inl_ver, sigW3_symm_inl_time, sigW3_symm_inl_bot,
      sigW3_symm_inl_top]
    incidence3_simp

theorem sigW3_out (f : PEdge3 T w h) (v' : PVert3 T (w + 1) h) (hv : v' ∈ (sigW3.symm (.inl f)).ends) :
    ∃ v, iotaW3 v = v' := by
  obtain ⟨vt, vx, vy⟩ := v'
  have hlt : (vx : ℕ) < w + 1 := by
    rcases f with ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩ <;>
    · simp only [sigW3_symm_inl_hor, sigW3_symm_inl_ver, sigW3_symm_inl_time, sigW3_symm_inl_bot,
        sigW3_symm_inl_top] at hv
      incidence3_simp at hv
      omega
  exact ⟨(vt, ⟨vx, hlt⟩, vy), by simp only [iotaW3, Prod.mk.injEq, true_and, and_true]; rfl⟩

theorem sigW3_bot_castSucc (t : Fin (T + 1)) (x : Fin (w + 1)) :
    (sigW3 (h := h)) (.bot t x.castSucc) = .inl (.bot t x) := by
  show Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XW3 T h) (.inr (.inr (.inr (.inr (t, false)))))
    (fun x' => .inl (.bot t x')) x.castSucc = _
  rw [Fin.lastCases_castSucc]

theorem sigW3_bot_last (t : Fin (T + 1)) :
    (sigW3 (w := w) (h := h)) (.bot t (Fin.last (w + 1))) = .inr (.inr (.inr (.inr (t, false)))) := by
  show Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XW3 T h) (.inr (.inr (.inr (.inr (t, false)))))
    (fun x' => .inl (.bot t x')) (Fin.last (w + 1)) = _
  rw [Fin.lastCases_last]

/-- The class of a glued configuration: the old class plus the new `b₁` half-edges. -/
theorem pcls3_glueW (a : PEdge3 T w h → ZMod 2) (b : XW3 T h → ZMod 2) :
    pcls3 (glueE sigW3 a b) = pcls3 a + ∑ t : Fin (T + 1), b (.inr (.inr (.inr (t, false)))) := by
  simp only [pcls3, glueE]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fin.sum_univ_castSucc]
  simp only [sigW3_bot_castSucc, sigW3_bot_last, Sum.elim_inl, Sum.elim_inr]

/-- **Monotonicity, `W → W + 1`**: adding a column of checks at a smooth side, in every layer, cannot decrease
the ML failure probability (for `0 ≤ q ≤ 1`). -/
theorem pML3_succ_w (T w h : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : pML3 T w h q ≤ pML3 T (w + 1) h q :=
  pML3_le_of_glue sigW3 iotaW3 iotaW3_inj sigW3_in sigW3_out _ pcls3_glueW hq0 hq1

end ColW

/-! ## `T → T + 1`: a new layer -/

section LayerT

variable {T w h : ℕ}

/-- Edges of the code with `T + 2` layers outside the code with `T + 1` layers: the horizontal and vertical edges of
the new layer, the time edges `(T,x,y)–(T+1,x,y)`, and the new layer's half-edges to `b₁` (`false`) and `b₂`
(`true`). -/
abbrev XT3 (w h : ℕ) :=
  (Fin w × Fin (h + 1)) ⊕ (Fin (w + 1) × Fin h) ⊕ (Fin (w + 1) × Fin (h + 1)) ⊕ (Fin (w + 1) × Bool)

/-- The edges of the code with `T + 2` layers as the edges of the code with `T + 1` layers plus the new edges. -/
def sigT3 : PEdge3 (T + 1) w h ≃ PEdge3 T w h ⊕ XT3 w h where
  toFun
    | .hor t x y => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XT3 w h) (.inr (.inl (x, y)))
        (fun t' => .inl (.hor t' x y)) t
    | .ver t x y => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XT3 w h) (.inr (.inr (.inl (x, y))))
        (fun t' => .inl (.ver t' x y)) t
    | .time t x y => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XT3 w h) (.inr (.inr (.inr (.inl (x, y)))))
        (fun t' => .inl (.time t' x y)) t
    | .bot t x => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XT3 w h) (.inr (.inr (.inr (.inr (x, false)))))
        (fun t' => .inl (.bot t' x)) t
    | .top t x => Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XT3 w h) (.inr (.inr (.inr (.inr (x, true)))))
        (fun t' => .inl (.top t' x)) t
  invFun
    | .inl (.hor t x y) => .hor t.castSucc x y
    | .inl (.ver t x y) => .ver t.castSucc x y
    | .inl (.time t x y) => .time t.castSucc x y
    | .inl (.bot t x) => .bot t.castSucc x
    | .inl (.top t x) => .top t.castSucc x
    | .inr (.inl (x, y)) => .hor (Fin.last (T + 1)) x y
    | .inr (.inr (.inl (x, y))) => .ver (Fin.last (T + 1)) x y
    | .inr (.inr (.inr (.inl (x, y)))) => .time (Fin.last T) x y
    | .inr (.inr (.inr (.inr (x, false)))) => .bot (Fin.last (T + 1)) x
    | .inr (.inr (.inr (.inr (x, true)))) => .top (Fin.last (T + 1)) x
  left_inv e := by
    rcases e with ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩ <;>
    · induction t using Fin.lastCases with
      | last => simp
      | cast t' => simp
  right_inv s := by
    rcases s with (⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩) | (⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, b⟩)
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · cases b <;> simp

theorem sigT3_symm_inl_hor (t : Fin (T + 1)) (x : Fin w) (y : Fin (h + 1)) :
    (sigT3 (T := T) (w := w) (h := h)).symm (.inl (.hor t x y)) = .hor t.castSucc x y := rfl
theorem sigT3_symm_inl_ver (t : Fin (T + 1)) (x : Fin (w + 1)) (y : Fin h) :
    (sigT3 (T := T) (w := w) (h := h)).symm (.inl (.ver t x y)) = .ver t.castSucc x y := rfl
theorem sigT3_symm_inl_time (t : Fin T) (x : Fin (w + 1)) (y : Fin (h + 1)) :
    (sigT3 (T := T) (w := w) (h := h)).symm (.inl (.time t x y)) = .time t.castSucc x y := rfl
theorem sigT3_symm_inl_bot (t : Fin (T + 1)) (x : Fin (w + 1)) :
    (sigT3 (T := T) (w := w) (h := h)).symm (.inl (.bot t x)) = .bot t.castSucc x := rfl
theorem sigT3_symm_inl_top (t : Fin (T + 1)) (x : Fin (w + 1)) :
    (sigT3 (T := T) (w := w) (h := h)).symm (.inl (.top t x)) = .top t.castSucc x := rfl

/-- The checks of the code with `T + 1` layers as the checks of the layers `0..T` of the code with `T + 2`
layers. -/
def iotaT3 (v : PVert3 T w h) : PVert3 (T + 1) w h := (v.1.castSucc, v.2.1, v.2.2)

theorem iotaT3_inj : Function.Injective (iotaT3 (T := T) (w := w) (h := h)) := by
  rintro ⟨t, x, y⟩ ⟨t', x', y'⟩ hv
  simp only [iotaT3, Prod.mk.injEq, Fin.castSucc_inj] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  rfl

theorem sigT3_in (f : PEdge3 T w h) (v : PVert3 T w h) :
    iotaT3 v ∈ (sigT3.symm (.inl f)).ends ↔ v ∈ f.ends := by
  obtain ⟨vt, vx, vy⟩ := v
  rcases f with ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩ <;>
  · simp only [iotaT3, sigT3_symm_inl_hor, sigT3_symm_inl_ver, sigT3_symm_inl_time, sigT3_symm_inl_bot,
      sigT3_symm_inl_top]
    incidence3_simp

theorem sigT3_out (f : PEdge3 T w h) (v' : PVert3 (T + 1) w h) (hv : v' ∈ (sigT3.symm (.inl f)).ends) :
    ∃ v, iotaT3 v = v' := by
  obtain ⟨vt, vx, vy⟩ := v'
  have hlt : (vt : ℕ) < T + 1 := by
    rcases f with ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩ <;>
    · simp only [sigT3_symm_inl_hor, sigT3_symm_inl_ver, sigT3_symm_inl_time, sigT3_symm_inl_bot,
        sigT3_symm_inl_top] at hv
      incidence3_simp at hv
      omega
  exact ⟨(⟨vt, hlt⟩, vx, vy), by simp only [iotaT3, Prod.mk.injEq, and_true]; rfl⟩

theorem sigT3_bot_castSucc (t : Fin (T + 1)) (x : Fin (w + 1)) :
    (sigT3 (h := h)) (.bot t.castSucc x) = .inl (.bot t x) := by
  show Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XT3 w h) (.inr (.inr (.inr (.inr (x, false)))))
    (fun t' => .inl (.bot t' x)) t.castSucc = _
  rw [Fin.lastCases_castSucc]

theorem sigT3_bot_last (x : Fin (w + 1)) :
    (sigT3 (T := T) (h := h)) (.bot (Fin.last (T + 1)) x) = .inr (.inr (.inr (.inr (x, false)))) := by
  show Fin.lastCases (motive := fun _ => PEdge3 T w h ⊕ XT3 w h) (.inr (.inr (.inr (.inr (x, false)))))
    (fun t' => .inl (.bot t' x)) (Fin.last (T + 1)) = _
  rw [Fin.lastCases_last]

/-- The class of a glued configuration: the old class plus the new layer's `b₁` half-edges. -/
theorem pcls3_glueT (a : PEdge3 T w h → ZMod 2) (b : XT3 w h → ZMod 2) :
    pcls3 (glueE sigT3 a b) = pcls3 a + ∑ x : Fin (w + 1), b (.inr (.inr (.inr (x, false)))) := by
  simp only [pcls3, glueE]
  rw [Fin.sum_univ_castSucc]
  simp only [sigT3_bot_castSucc, sigT3_bot_last, Sum.elim_inl, Sum.elim_inr]

/-- **Monotonicity, `T → T + 1`**: one more noisy round cannot decrease the ML failure probability (for
`0 ≤ q ≤ 1`). The code with `T` noisy rounds is the code with `T + 1` noisy rounds restricted to the layers `0..T`;
its decoder draws the new layer's edges and the time edges into it, forms the bigger syndrome (including the new
perfect final round), decodes by ML and corrects by the new layer's `b₁` half-edges. -/
theorem pML3_succ_t (T w h : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : pML3 T w h q ≤ pML3 (T + 1) w h q :=
  pML3_le_of_glue sigT3 iotaT3 iotaT3_inj sigT3_in sigT3_out _ pcls3_glueT hq0 hq1

end LayerT

/-! ## Monotonicity in the size -/

theorem pML3_antitone_h (T w : ℕ) (q : ℝ) : Antitone fun h => pML3 T w h q :=
  antitone_nat_of_succ_le fun h => pML3_succ_h T w h q

theorem pML3_monotone_w (T h : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Monotone fun w => pML3 T w h q :=
  monotone_nat_of_le_succ fun w => pML3_succ_w T w h hq0 hq1

theorem pML3_monotone_t (w h : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Monotone fun T => pML3 T w h q :=
  monotone_nat_of_le_succ fun T => pML3_succ_t T w h hq0 hq1

/-- **Monotonicity in the size**: more rounds (`T ≤ T'`), wider (`w ≤ w'`) and lower (`h' ≤ h`) codes have a larger
ML failure probability. Used with `T + 1` and `W` rounded up and `H` rounded down to multiples of the block side. -/
theorem pML3_mono_size {T T' w w' h h' : ℕ} (hT : T ≤ T') (hw : w ≤ w') (hh : h' ≤ h) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : pML3 T w h q ≤ pML3 T' w' h' q :=
  (pML3_antitone_h T w q hh).trans <| (pML3_monotone_w T h' hq0 hq1 hw).trans (pML3_monotone_t w' h' hq0 hq1 hT)

end QECD1
