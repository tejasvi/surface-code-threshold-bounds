import QECML.TwoD.T2Trick
import QECML.TwoD.T2Fam

/-!
# The T2 summation over the skeleton class

Skeleton weights (`skW`, module `T2Trick`) depend on a family only through its key `famKey f` (landing root, counted
blocks, exit cover). The sum over skeletons is organised along the skeleton: the bottom part, then a transfer over
the families (each a jump with `(R)`, the landing root's `ε`, the family factor), then the top part.

This file: family keys and the tail weight on keys (`tailWK`), the row sum of jump weights (`row_sum_le`), and the
top-part sum (`top_sum_le`).
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-- The key of a family: its landing root, its counted blocks, its exit cover. -/
def famKey (f : G.CRoute × G.Wit) : G.Block × List G.Block × G.Block := (f.1.r 0, f.1.blocks ++ f.2.blocks, f.1.last)

/-- The weight of a family key entered from the cover `c`. -/
noncomputable def wFamK (ε lam mu s off : ℝ) (c : G.Block) (k : G.Block × List G.Block × G.Block) : ℝ :=
  ε ^ k.2.1.length * Real.exp (-lam * (bl1 c k.1 : ℝ) + s * ((k.1.2.val : ℝ) - (c.2.val : ℝ)) + lam * off +
    mu * (bl1 k.1 k.2.2 : ℝ) + s * ((k.2.2.2.val : ℝ) - (k.1.2.val : ℝ)))

theorem wFam_eq_wFamK (ε lam mu s off : ℝ) (c : G.Block) (f : G.CRoute × G.Wit) :
    wFam ε lam mu s off c f = wFamK ε lam mu s off c (famKey f) := rfl

/-- The tail weight on keys. -/
noncomputable def tailWK (ε lam mu s off : ℝ) :
    G.Block → List (G.Block × List G.Block × G.Block) → G.Block → List G.Move → Bool → ℝ
  | c, [], et, mst, tf => wTop ε lam mu s c et mst tf
  | c, k :: ks, et, mst, tf => wFamK ε lam mu s off c k * tailWK ε lam mu s off k.2.2 ks et mst tf

theorem tailW_eq_tailWK (ε lam mu s off : ℝ) (et : G.Block) (mst : List G.Move) (tf : Bool) :
    ∀ (fams : List (G.CRoute × G.Wit)) (c : G.Block),
      tailW ε lam mu s off c fams et mst tf = tailWK ε lam mu s off c (fams.map famKey) et mst tf
  | [], c => rfl
  | f :: rest, c => by
    rw [tailW, List.map_cons, tailWK, wFam_eq_wFamK, tailW_eq_tailWK ε lam mu s off et mst tf rest f.1.last]
    rfl

/-! ### Jump weights -/

/-- The weight of a jump from `c` to `e` with tilts `λ`, `s`. -/
noncomputable def jwt (lam s : ℝ) (c e : G.Block) : ℝ :=
  Real.exp (-lam * (bl1 c e : ℝ) + s * ((e.2.val : ℝ) - (c.2.val : ℝ)))

theorem jwt_eq_jw (c e : G.Block) : jwt 0.041 0.02 c e = jw c e := by
  simp only [jwt, jw]
  rfl

theorem jwt_nonneg (lam s : ℝ) (c e : G.Block) : 0 ≤ jwt lam s c e := (Real.exp_pos _).le

/-- **Jumps into one row at or above the cover**: at most `Sx = (1 + qUp)/(1 - qUp)`. -/
theorem row_sum_le (c : G.Block) (y : Fin G.ny) (hy : c.2.val ≤ y.val) (E : Finset G.Block)
    (hE : ∀ e ∈ E, e.2 = y) : ∑ e ∈ E, jwt 0.041 0.02 c e ≤ (1 + (qUp : ℝ)) / (1 - qUp) := by
  obtain ⟨hq0, hq1, -⟩ := rq_bounds
  have hle : ∀ e ∈ E, jwt 0.041 0.02 c e ≤ (qUp : ℝ) ^ ((e.1.val : ℤ) - c.1.val).natAbs := by
    intro e he
    have hey := hE e he
    have hdy : c.2.val ≤ e.2.val := by rw [hey]; exact hy
    have hb : bl1 c e = ((e.1.val : ℤ) - c.1.val).natAbs + (e.2.val - c.2.val) := by
      simp only [bl1, ndist_eq_natAbs]
      omega
    unfold jwt
    rw [hb]
    have e1 : -0.041 * ((((e.1.val : ℤ) - c.1.val).natAbs + (e.2.val - c.2.val) : ℕ) : ℝ) +
        0.02 * ((e.2.val : ℝ) - (c.2.val : ℝ)) ≤ ((((e.1.val : ℤ) - c.1.val).natAbs : ℕ) : ℝ) * (-0.041) := by
      have h1 : ((e.2.val - c.2.val : ℕ) : ℝ) = (e.2.val : ℝ) - (c.2.val : ℝ) := by
        rw [Nat.cast_sub hdy]
      push_cast
      rw [h1]
      have h2 : (0 : ℝ) ≤ (e.2.val : ℝ) - (c.2.val : ℝ) := by
        have : ((c.2.val : ℕ) : ℝ) ≤ ((e.2.val : ℕ) : ℝ) := by exact_mod_cast hdy
        linarith
      nlinarith
    refine (Real.exp_le_exp.2 e1).trans ?_
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_lam_le _
  have hinj : ∀ e ∈ E, ∀ e' ∈ E, ((e.1.val : ℤ) - c.1.val) = ((e'.1.val : ℤ) - c.1.val) → e = e' := by
    intro e he e' he' h
    exact Prod.ext (Fin.ext (by omega)) (by rw [hE e he, hE e' he'])
  calc ∑ e ∈ E, jwt 0.041 0.02 c e ≤ ∑ e ∈ E, (qUp : ℝ) ^ ((e.1.val : ℤ) - c.1.val).natAbs :=
        Finset.sum_le_sum hle
    _ = ∑ x ∈ E.image (fun e : G.Block => ((e.1.val : ℤ) - c.1.val)), (qUp : ℝ) ^ x.natAbs :=
        (Finset.sum_image (f := fun x : ℤ => (qUp : ℝ) ^ x.natAbs) hinj).symm
    _ ≤ (1 + (qUp : ℝ)) / (1 - qUp) := sum_abs_pow_le hq0 hq1 _

/-! ### The top part -/

theorem wTop_eq (ε lam mu s : ℝ) (c et : G.Block) (mst : List G.Move) (tf : Bool) :
    wTop ε lam mu s c et mst tf = (if tf then ε else 1) * jwt lam s c et * gwt (t2g ε mu s) et mst := by
  rw [wTop, gwt_t2g, Xt, jwt]
  rw [show -lam * (bl1 c et : ℝ) + s * ((et.2.val : ℝ) - (c.2.val : ℝ)) + mu * (rnorm et mst : ℝ) +
      s * (((endBlock et mst).2.val : ℝ) - (et.2.val : ℝ)) =
      (-lam * (bl1 c et : ℝ) + s * ((et.2.val : ℝ) - (c.2.val : ℝ))) +
      (mu * (rnorm et mst : ℝ) + s * (((endBlock et mst).2.val : ℝ) - (et.2.val : ℝ))) by ring, Real.exp_add]
  ring

/-- The validity of a top part entered from a cover (the jump has `(R)` unless exempt). -/
def TopOK (ex : Bool) (c et : G.Block) (mst : List G.Move) (tf : Bool) : Prop :=
  if tf then (ex = false → 9 ≤ G.blockDist c et) ∧ GramFrom G.D (G.D - 1 + 4) (G.D - 1 + 12) .A et mst
  else mst = [] ∧ et.2.val + 1 = G.ny

/-- The top factor: `J ε 3.85 + Sx`, with `J = Jbd` (jump with `(R)`) or `JFbd` (exempt jump). -/
noncomputable def topB (ex : Bool) : ℝ :=
  (if ex then JFbd else Jbd) * 5e-4 * 3.85 + (1 + (qUp : ℝ)) / (1 - qUp)

theorem Jbd_nonneg : 0 ≤ Jbd := by
  obtain ⟨hq0, hq1, hp0, hp1, hm0, hm1⟩ := rq_bounds
  unfold Jbd
  have h1 : 0 ≤ (1 - (qUp : ℝ)) := by linarith
  have h2 : 0 ≤ (1 - (qpUp : ℝ)) := by linarith
  have h3 : 0 ≤ (1 - (qmUp : ℝ)) := by linarith
  have hs : 0 ≤ ∑ k ∈ Finset.range 9, (qUp : ℝ) ^ k + ∑ k ∈ Finset.Icc 1 8, (qUp : ℝ) ^ k :=
    add_nonneg (Finset.sum_nonneg fun k _ => pow_nonneg hq0 k) (Finset.sum_nonneg fun k _ => pow_nonneg hq0 k)
  positivity

theorem JFbd_nonneg : 0 ≤ JFbd := by
  obtain ⟨hq0, hq1, hp0, hp1, hm0, hm1⟩ := rq_bounds
  unfold JFbd
  have h1 : 0 ≤ (1 - (qUp : ℝ)) := by linarith
  have h2 : 0 ≤ (1 - (qpUp : ℝ)) := by linarith
  have h3 : 0 ≤ (1 - (qmUp : ℝ)) := by linarith
  positivity

/-- **The top-part sum**: over any finite set of valid top parts entered from `c`, the weights sum to at most
`topB ex`. -/
theorem top_sum_le (hD : G.D = 5) (ex : Bool) (c : G.Block) (T : Finset (G.Block × List G.Move × Bool))
    (hT : ∀ t ∈ T, TopOK ex c t.1 t.2.1 t.2.2) :
    ∑ t ∈ T, wTop 5e-4 0.041 0.04305 0.02 c t.1 t.2.1 t.2.2 ≤ topB ex := by
  rw [← Finset.sum_filter_add_sum_filter_not T (fun t => t.2.2 = true)]
  unfold topB
  refine add_le_add ?_ ?_
  · -- counted top roots: J ε 3.85
    set T1 := T.filter (fun t => t.2.2 = true) with hT1
    have hw : ∀ t ∈ T1, wTop 5e-4 0.041 0.04305 0.02 c t.1 t.2.1 t.2.2 =
        5e-4 * jwt 0.041 0.02 c t.1 * gwt (t2g 5e-4 0.04305 0.02) t.1 t.2.1 := by
      intro t ht
      rw [wTop_eq, ite_eq_left (Finset.mem_filter.1 ht).2]
    rw [Finset.sum_congr rfl hw, ← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := T1.image Prod.fst)
      (fun t ht => Finset.mem_image_of_mem _ ht)]
    have hfib : ∀ et ∈ T1.image Prod.fst, ∑ t ∈ T1 with t.1 = et,
        5e-4 * jwt 0.041 0.02 c t.1 * gwt (t2g 5e-4 0.04305 0.02) t.1 t.2.1 ≤ jwt 0.041 0.02 c et * (5e-4 * 3.85) := by
      intro et _
      have heq : ∀ t ∈ T1.filter (fun t => t.1 = et), 5e-4 * jwt 0.041 0.02 c t.1 *
          gwt (t2g 5e-4 0.04305 0.02) t.1 t.2.1 = 5e-4 * jwt 0.041 0.02 c et *
          (gwt (t2g 5e-4 0.04305 0.02) et t.2.1 * (fun _ => (1 : ℝ)) (finalSt .A et t.2.1)) := by
        intro t ht
        rw [(Finset.mem_filter.1 ht).2]
        ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
      -- the top route words from `et`, injectively by their move lists
      have hinj : Set.InjOn (fun t : G.Block × List G.Move × Bool => t.2.1)
          ((T1.filter (fun t => t.1 = et) : Finset _) : Set (G.Block × List G.Move × Bool)) := by
        intro t ht t' ht' h
        have h1 := (Finset.mem_filter.1 ht).2
        have h2 := (Finset.mem_filter.1 ht').2
        have h3 := (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).2
        have h4 := (Finset.mem_filter.1 (Finset.mem_filter.1 ht').1).2
        exact Prod.ext (h1.trans h2.symm) (Prod.ext h (h3.trans h4.symm))
      rw [← Finset.sum_image (f := fun r => gwt (t2g 5e-4 0.04305 0.02) et r * (fun _ => (1 : ℝ)) (finalSt .A et r))
        hinj]
      set R := (T1.filter (fun t => t.1 = et)).image (fun t : G.Block × List G.Move × Bool => t.2.1)
      have hR : ∀ r ∈ R, GramFrom G.D (G.D - 1 + 4) (G.D - 1 + 12) .A et r ∧ r.length ≤ R.sup List.length := by
        intro r hr
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hr
        have htT := (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).1
        have htf := (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).2
        have hte := (Finset.mem_filter.1 ht).2
        have hok := hT t htT
        unfold TopOK at hok
        rw [ite_eq_left htf] at hok
        refine ⟨hte ▸ hok.2, Finset.le_sup (f := List.length) hr⟩
      have h1 := sum_gwtE_le G.D (G.D - 1 + 4) (G.D - 1 + 12) (t2g_nonneg (ε := 5e-4) (by norm_num) 0.04305 0.02)
        (e := fun _ => (1 : ℝ)) (fun _ => zero_le_one) (R.sup List.length) .A et R hR
      have h2 := route_any_le hD (R.sup List.length) .A et
      have hj := jwt_nonneg 0.041 0.02 c et
      have h3 : ∑ r ∈ R, gwt (t2g 5e-4 0.04305 0.02) et r * (fun _ => (1 : ℝ)) (finalSt .A et r) ≤ 3.85 :=
        h1.trans h2
      nlinarith
    calc ∑ et ∈ T1.image Prod.fst, ∑ t ∈ T1 with t.1 = et,
          5e-4 * jwt 0.041 0.02 c t.1 * gwt (t2g 5e-4 0.04305 0.02) t.1 t.2.1
        ≤ ∑ et ∈ T1.image Prod.fst, jwt 0.041 0.02 c et * (5e-4 * 3.85) := Finset.sum_le_sum hfib
      _ = (∑ et ∈ T1.image Prod.fst, jwt 0.041 0.02 c et) * (5e-4 * 3.85) := by rw [Finset.sum_mul]
      _ ≤ (if ex then JFbd else Jbd) * (5e-4 * 3.85) := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          simp only [jwt_eq_jw]
          cases ex with
          | true => exact jump_full_le c _
          | false =>
            refine jump_le c _ fun et het => ?_
            obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 het
            have hok := hT t (Finset.mem_filter.1 ht).1
            unfold TopOK at hok
            rw [ite_eq_left (Finset.mem_filter.1 ht).2] at hok
            exact hok.1 rfl
      _ = (if ex then JFbd else Jbd) * 5e-4 * 3.85 := by ring
  · -- uncounted top roots in the top row: Sx
    set T2 := T.filter (fun t => ¬ t.2.2 = true) with hT2
    have hw : ∀ t ∈ T2, wTop 5e-4 0.041 0.04305 0.02 c t.1 t.2.1 t.2.2 = jwt 0.041 0.02 c t.1 := by
      intro t ht
      have htf := (Finset.mem_filter.1 ht).2
      have hok := hT t (Finset.mem_filter.1 ht).1
      unfold TopOK at hok
      rw [ite_eq_right htf] at hok
      rw [wTop_eq, ite_eq_right htf, hok.1]
      simp [gwt]
    rw [Finset.sum_congr rfl hw]
    have hny : 1 ≤ G.ny := G.hny
    have hinj : Set.InjOn (fun t : G.Block × List G.Move × Bool => t.1) ((T2 : Finset _) : Set _) := by
      intro t ht t' ht' h
      have hf1 := (Finset.mem_filter.1 ht).2
      have hf2 := (Finset.mem_filter.1 ht').2
      have hok1 := hT t (Finset.mem_filter.1 ht).1
      have hok2 := hT t' (Finset.mem_filter.1 ht').1
      unfold TopOK at hok1 hok2
      rw [ite_eq_right hf1] at hok1
      rw [ite_eq_right hf2] at hok2
      have e3 : t.2.2 = t'.2.2 := by
        cases h1 : t.2.2 <;> cases h2 : t'.2.2 <;> simp_all
      exact Prod.ext h (Prod.ext (hok1.1.trans hok2.1.symm) e3)
    rw [← Finset.sum_image (f := fun e => jwt 0.041 0.02 c e) hinj]
    refine row_sum_le c ⟨G.ny - 1, by omega⟩ (by have := c.2.isLt; simp; omega) _ fun e he => ?_
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 he
    have hok := hT t (Finset.mem_filter.1 ht).1
    unfold TopOK at hok
    rw [ite_eq_right (Finset.mem_filter.1 ht).2] at hok
    exact Fin.ext (by simp; omega)

end S3Geom

end QECML
