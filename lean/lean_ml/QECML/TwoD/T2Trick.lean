import QECML.TwoD.T2Count
import QECML.TwoD.T2Fac

/-!
# The T2 summation: the λ-trick and the height tilt on a valid T2 skeleton

For a valid skeleton (`T2Sk.OK` with metric ratio `κ ≤ κ̄` and boundary constant `cH ≤ c̄H`), the exchange inequality
in block units gives `1 ≤ e^{λ (RHS - Σ jumps)}` and the height bound gives `1 ≤ e^{s (climb - (n_y - H0))}`. Hence
(`skel_trick`)

  `ε^{|counted|} ≤ skW sk · e^{λ c_ends} · e^{-s (n_y - H0)}`,   `c_ends = 2D + κ̄ D + κ̄ h_s + κ̄ (h_s + A1 + 1) + c̄H`,

where `skW sk` is a product along the skeleton: the bottom route word (T2 move weights, `μ = λ κ̄`), then for each
intermediate family the jump weight `e^{-λ |r0 - c|_1 + s (r0_y - c_y)}`, the factor `e^{λ 2D (1 + κ̄)}`, `ε` per
counted block of the family and `e^{μ |last - r0|_1 + s (last_y - r0_y)}`, and finally the jump to the top root, its `ε`
(if counted) and the top route word.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

theorem bl1_eq_bdl1 (b b' : G.Block) : bl1 b b' = bdl1 b b' := rfl

/-! ### Weights along a skeleton -/

/-- The exponent of an intermediate family entered from the cover `c`: its jump, the factor `λ off`, its span tilt
and its height tilt. -/
noncomputable def Xf (lam mu s off : ℝ) (c : G.Block) (f : G.CRoute × G.Wit) : ℝ :=
  -lam * (bl1 c (f.1.r 0) : ℝ) + s * (((f.1.r 0).2.val : ℝ) - (c.2.val : ℝ)) + lam * off +
    mu * (bl1 (f.1.r 0) f.1.last : ℝ) + s * ((f.1.last.2.val : ℝ) - ((f.1.r 0).2.val : ℝ))

/-- The exponent of the top part entered from the cover `c`. -/
noncomputable def Xt (lam mu s : ℝ) (c et : G.Block) (mst : List G.Move) : ℝ :=
  -lam * (bl1 c et : ℝ) + s * ((et.2.val : ℝ) - (c.2.val : ℝ)) + mu * (rnorm et mst : ℝ) +
    s * (((endBlock et mst).2.val : ℝ) - (et.2.val : ℝ))

/-- The weight of an intermediate family entered from the cover `c`. -/
noncomputable def wFam (ε lam mu s off : ℝ) (c : G.Block) (f : G.CRoute × G.Wit) : ℝ :=
  ε ^ (f.1.blocks ++ f.2.blocks).length * Real.exp (Xf lam mu s off c f)

/-- The weight of the top part entered from the cover `c`. -/
noncomputable def wTop (ε lam mu s : ℝ) (c et : G.Block) (mst : List G.Move) (tf : Bool) : ℝ :=
  (if tf then ε else 1) * ε ^ mst.length * Real.exp (Xt lam mu s c et mst)

/-- The weight of the part of a skeleton after a cover `c`: its families, then its top part. -/
noncomputable def tailW (ε lam mu s off : ℝ) :
    G.Block → List (G.CRoute × G.Wit) → G.Block → List G.Move → Bool → ℝ
  | c, [], et, mst, tf => wTop ε lam mu s c et mst tf
  | c, f :: rest, et, mst, tf => wFam ε lam mu s off c f * tailW ε lam mu s off f.1.last rest et mst tf

/-- The weight of a skeleton. -/
noncomputable def skW (ε lam mu s off : ℝ) (sk : G.T2Sk) : ℝ :=
  gwt (t2g ε mu s) sk.b0 sk.ms0 * tailW ε lam mu s off (endBlock sk.b0 sk.ms0) sk.fams sk.et sk.mst sk.tf

/-- The exponent of the tail (recursive). -/
noncomputable def tailE (lam mu s off : ℝ) :
    G.Block → List (G.CRoute × G.Wit) → G.Block → List G.Move → ℝ
  | c, [], et, mst => Xt lam mu s c et mst
  | c, f :: rest, et, mst => Xf lam mu s off c f + tailE lam mu s off f.1.last rest et mst

/-- The number of counted blocks after a cover. -/
def tailLen (fams : List (G.CRoute × G.Wit)) (mst : List G.Move) (tf : Bool) : ℕ :=
  (fams.map fun f => (f.1.blocks ++ f.2.blocks).length).sum + ((if tf then 1 else 0) + mst.length)

theorem tailW_eq (ε lam mu s off : ℝ) (et : G.Block) (mst : List G.Move) (tf : Bool) :
    ∀ (fams : List (G.CRoute × G.Wit)) (c : G.Block),
      tailW ε lam mu s off c fams et mst tf = ε ^ tailLen fams mst tf * Real.exp (tailE lam mu s off c fams et mst)
  | [], c => by
    simp only [tailW, wTop, tailLen, tailE, List.map_nil, List.sum_nil, zero_add]
    rw [pow_add]
    split_ifs <;> simp
  | f :: rest, c => by
    rw [tailW, tailW_eq ε lam mu s off et mst tf rest f.1.last, wFam, tailE, Real.exp_add]
    simp only [tailLen, List.map_cons, List.sum_cons]
    rw [add_assoc, pow_add]
    ring

/-! ### Closed form of the tail exponent -/

/-- The jumps after a cover `c`. -/
def jumpsFrom (c : G.Block) (fams : List (G.CRoute × G.Wit)) (et : G.Block) : List (G.Block × G.Block) :=
  (c :: fams.map (fun f => f.1.last)).zip (fams.map (fun f => f.1.r 0) ++ [et])

theorem jumpsFrom_nil (c et : G.Block) : jumpsFrom c [] et = [(c, et)] := rfl

theorem jumpsFrom_cons (c : G.Block) (f : G.CRoute × G.Wit) (rest : List (G.CRoute × G.Wit)) (et : G.Block) :
    jumpsFrom c (f :: rest) et = (c, f.1.r 0) :: jumpsFrom f.1.last rest et := by
  simp [jumpsFrom]

/-- The sum of the jump lengths after `c`. -/
def jsum (c : G.Block) (fams : List (G.CRoute × G.Wit)) (et : G.Block) : ℕ :=
  ((jumpsFrom c fams et).map fun q => bl1 q.1 q.2).sum

/-- The sum of the family spans. -/
def ssum (fams : List (G.CRoute × G.Wit)) : ℕ := (fams.map fun f => bl1 (f.1.r 0) f.1.last).sum

theorem jsum_nil (c et : G.Block) : jsum c [] et = bl1 c et := by
  simp [jsum, jumpsFrom_nil]

theorem jsum_cons (c : G.Block) (f : G.CRoute × G.Wit) (rest : List (G.CRoute × G.Wit)) (et : G.Block) :
    jsum c (f :: rest) et = bl1 c (f.1.r 0) + jsum f.1.last rest et := by
  simp [jsum, jumpsFrom_cons]

theorem ssum_cons (f : G.CRoute × G.Wit) (rest : List (G.CRoute × G.Wit)) :
    ssum (f :: rest) = bl1 (f.1.r 0) f.1.last + ssum rest := by
  simp [ssum]

theorem tailE_eq (lam mu s off : ℝ) (et : G.Block) (mst : List G.Move) :
    ∀ (fams : List (G.CRoute × G.Wit)) (c : G.Block),
      tailE lam mu s off c fams et mst = -lam * (jsum c fams et : ℝ) + mu * (ssum fams : ℝ) +
        lam * off * (fams.length : ℝ) + mu * (rnorm et mst : ℝ) +
        s * (((endBlock et mst).2.val : ℝ) - (c.2.val : ℝ))
  | [], c => by
    simp only [tailE, Xt, jsum_nil, ssum, List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero]
    ring
  | f :: rest, c => by
    rw [tailE, tailE_eq lam mu s off et mst rest f.1.last, jsum_cons, ssum_cons, List.length_cons, Xf]
    push_cast
    ring

/-! ### The λ-trick -/

theorem row_le_bdl1 (b b' : G.Block) : (b'.2.val : ℝ) - (b.2.val : ℝ) ≤ (bdl1 b b' : ℝ) := by
  have h : b'.2.val ≤ b.2.val + bdl1 b b' := by
    simp only [bdl1, ndist]
    omega
  have h' : ((b'.2.val : ℕ) : ℝ) ≤ ((b.2.val + bdl1 b b' : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

theorem counted_length (sk : G.T2Sk) : sk.counted.length = sk.ms0.length + tailLen sk.fams sk.mst sk.tf := by
  simp only [T2Sk.counted, tailLen, List.length_append, List.length_map, List.length_flatMap]
  split_ifs <;> simp

theorem jumps_eq (sk : G.T2Sk) : sk.jumps = jumpsFrom (endBlock sk.b0 sk.ms0) sk.fams sk.et := rfl

/-- **The λ-trick and the height tilt on a valid skeleton.** -/
theorem skel_trick (sk : G.T2Sk) {D A0 A1 hs Sw : ℕ} {κ cH : ℝ} (hok : sk.OK D A0 A1 hs Sw κ cH)
    {ε lam s kb cb : ℝ} (hε : 0 ≤ ε) (hlam : 0 ≤ lam) (hs0 : 0 ≤ s) (hκ0 : 0 ≤ κ) (hκ : κ ≤ kb) (hcH : cH ≤ cb) :
    ε ^ sk.counted.length ≤ skW ε lam (lam * kb) s (2 * D * (1 + kb)) sk *
      Real.exp (lam * (2 * D + kb * D + kb * hs + kb * (hs + A1 + 1) + cb)) *
      Real.exp (-s * ((G.ny : ℝ) - (2 * hs + A1 + 1))) := by
  obtain ⟨⟨hb0, -⟩, -, ⟨-, -, -, -, -, -, hend, -⟩, -, hmet, -⟩ := hok
  set σ0 := endBlock sk.b0 sk.ms0 with hσ0
  set e1 := endBlock sk.et sk.mst with he1
  -- the weight in closed form
  have hW : skW ε lam (lam * kb) s (2 * D * (1 + kb)) sk = ε ^ sk.counted.length *
      Real.exp (lam * kb * (rnorm sk.b0 sk.ms0 : ℝ) + s * ((σ0.2.val : ℝ) - (sk.b0.2.val : ℝ)) +
        (-lam * (jsum σ0 sk.fams sk.et : ℝ) + lam * kb * (ssum sk.fams : ℝ) +
          lam * (2 * D * (1 + kb)) * (sk.fams.length : ℝ) + lam * kb * (rnorm sk.et sk.mst : ℝ) +
          s * ((e1.2.val : ℝ) - (σ0.2.val : ℝ)))) := by
    rw [skW, gwt_t2g, tailW_eq, tailE_eq, counted_length, pow_add, ← hσ0, ← he1]
    conv_rhs => rw [Real.exp_add]
    ring
  rw [hW]
  -- the exponent is nonnegative after the two tilts
  have hmet' : (jsum σ0 sk.fams sk.et : ℝ) ≤ κ * (ssum sk.fams : ℝ) + 2 * D * (sk.fams.length + 1) +
      2 * D * κ * sk.fams.length + κ * ((σ0.2.val : ℝ) + D) + κ * ((G.ny : ℝ) - sk.et.2.val) + cH := hmet
  have hσr : (σ0.2.val : ℝ) ≤ (hs : ℝ) + (rnorm sk.b0 sk.ms0 : ℝ) := by
    have h1 := row_le_bdl1 sk.b0 σ0
    have h2 : (bdl1 sk.b0 σ0 : ℝ) ≤ (rnorm sk.b0 sk.ms0 : ℝ) := by exact_mod_cast bdl1_le_rnorm sk.b0 sk.ms0
    have h3 : (sk.b0.2.val : ℝ) ≤ hs := by exact_mod_cast hb0
    linarith
  have hetr : (G.ny : ℝ) - sk.et.2.val ≤ (hs : ℝ) + A1 + 1 + (rnorm sk.et sk.mst : ℝ) := by
    have h1 := row_le_bdl1 sk.et e1
    have h2 : (bdl1 sk.et e1 : ℝ) ≤ (rnorm sk.et sk.mst : ℝ) := by exact_mod_cast bdl1_le_rnorm sk.et sk.mst
    have h3 : (G.ny : ℝ) ≤ (e1.2.val : ℝ) + 1 + hs + A1 := by exact_mod_cast hend
    linarith
  have hclimb : (G.ny : ℝ) - (2 * hs + A1 + 1) ≤ (e1.2.val : ℝ) - (sk.b0.2.val : ℝ) := by
    have h3 : (G.ny : ℝ) ≤ (e1.2.val : ℝ) + 1 + hs + A1 := by exact_mod_cast hend
    have h4 : (sk.b0.2.val : ℝ) ≤ hs := by exact_mod_cast hb0
    linarith
  have hny : (sk.et.2.val : ℝ) ≤ G.ny := by exact_mod_cast sk.et.2.isLt.le
  have hss : (0 : ℝ) ≤ ssum sk.fams := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ sk.fams.length := Nat.cast_nonneg _
  have hσ0nn : (0 : ℝ) ≤ (σ0.2.val : ℝ) + D := by positivity
  -- monotonicity of the metric constraint in κ, cH
  have hmono : κ * (ssum sk.fams : ℝ) + 2 * D * (sk.fams.length + 1) + 2 * D * κ * sk.fams.length +
      κ * ((σ0.2.val : ℝ) + D) + κ * ((G.ny : ℝ) - sk.et.2.val) + cH ≤
      kb * (ssum sk.fams : ℝ) + 2 * D * (sk.fams.length + 1) + 2 * D * kb * sk.fams.length +
      kb * ((σ0.2.val : ℝ) + D) + kb * ((G.ny : ℝ) - sk.et.2.val) + cb := by
    have h1 := mul_le_mul_of_nonneg_right hκ hss
    have h2 := mul_le_mul_of_nonneg_right hκ hm
    have h3 := mul_le_mul_of_nonneg_right hκ hσ0nn
    have h4 := mul_le_mul_of_nonneg_right hκ (sub_nonneg.2 hny)
    have hD0 : (0 : ℝ) ≤ 2 * D := by positivity
    have h2' := mul_le_mul_of_nonneg_left h2 hD0
    nlinarith
  have hkb : 0 ≤ kb := hκ0.trans hκ
  have key : 0 ≤ lam * kb * (rnorm sk.b0 sk.ms0 : ℝ) + s * ((σ0.2.val : ℝ) - (sk.b0.2.val : ℝ)) +
      (-lam * (jsum σ0 sk.fams sk.et : ℝ) + lam * kb * (ssum sk.fams : ℝ) +
        lam * (2 * D * (1 + kb)) * (sk.fams.length : ℝ) + lam * kb * (rnorm sk.et sk.mst : ℝ) +
        s * ((e1.2.val : ℝ) - (σ0.2.val : ℝ))) +
      lam * (2 * D + kb * D + kb * hs + kb * (hs + A1 + 1) + cb) +
      -s * ((G.ny : ℝ) - (2 * hs + A1 + 1)) := by
    have t1 : 0 ≤ lam * (kb * (ssum sk.fams : ℝ) + kb * (rnorm sk.b0 sk.ms0 : ℝ) + kb * (rnorm sk.et sk.mst : ℝ) +
        2 * D * (1 + kb) * sk.fams.length + (2 * D + kb * D + kb * hs + kb * (hs + A1 + 1) + cb) -
        (jsum σ0 sk.fams sk.et : ℝ)) := by
      refine mul_nonneg hlam ?_
      have u1 := mul_le_mul_of_nonneg_left hσr hkb
      have u2 := mul_le_mul_of_nonneg_left hetr hkb
      nlinarith
    have t2 : 0 ≤ s * ((e1.2.val : ℝ) - (sk.b0.2.val : ℝ) - ((G.ny : ℝ) - (2 * hs + A1 + 1))) :=
      mul_nonneg hs0 (by linarith)
    nlinarith
  have hpow : 0 ≤ ε ^ sk.counted.length := pow_nonneg hε _
  calc ε ^ sk.counted.length = ε ^ sk.counted.length * 1 := (mul_one _).symm
    _ ≤ ε ^ sk.counted.length * (Real.exp (lam * kb * (rnorm sk.b0 sk.ms0 : ℝ) +
          s * ((σ0.2.val : ℝ) - (sk.b0.2.val : ℝ)) +
          (-lam * (jsum σ0 sk.fams sk.et : ℝ) + lam * kb * (ssum sk.fams : ℝ) +
            lam * (2 * D * (1 + kb)) * (sk.fams.length : ℝ) + lam * kb * (rnorm sk.et sk.mst : ℝ) +
            s * ((e1.2.val : ℝ) - (σ0.2.val : ℝ)))) *
          Real.exp (lam * (2 * D + kb * D + kb * hs + kb * (hs + A1 + 1) + cb)) *
          Real.exp (-s * ((G.ny : ℝ) - (2 * hs + A1 + 1)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hpow
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.one_le_exp key
    _ = _ := by ring

end S3Geom

end QECML
