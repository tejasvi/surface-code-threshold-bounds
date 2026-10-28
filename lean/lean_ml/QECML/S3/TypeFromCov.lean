import QECML.S3.Covariance
import QECML.S3.Hypotheses
import QECML.TwoD.LemmaA

/-!
# Equality of block types from translation covariance

* `Hcov` (named hypothesis on the stage-1 rules; (R2) translation covariance, validated by V2, made explicit): the
  stage-1 output of a block depends only on its window graph up to translation by whole blocks.
* `prob_comp_inj`: the product measure pushed forward along the restriction to an injective image is the product
  measure, so the probability of an event of the restricted errors does not depend on the larger code.
* `htype_of_hcov`: for `R < L`, `Hcov` implies `Htype`: every sampled block of every code with `n_x, n_y ≥ 5` has
  the bad probability of its type's reference block on the 5 × 5 reference code.
-/

open Finset Classical

namespace QECML

/-- **Restriction along an injective map**: the product measure on `ι₁` pushed forward by `E ↦ E ∘ f` is the
product measure on `ι₂`. -/
theorem sum_bernProd_comp {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (q : ℝ) {f : ι₂ → ι₁}
    (hf : Function.Injective f) (g : (ι₂ → ZMod 2) → ℝ) :
    ∑ E : ι₁ → ZMod 2, bernProd q E * g (E ∘ f) = ∑ E' : ι₂ → ZMod 2, bernProd q E' * g E' := by
  let σ : ι₁ ≃ ι₂ ⊕ {e // e ∉ Set.range f} :=
    (Equiv.sumCompl (· ∈ Set.range f)).symm.trans (Equiv.sumCongr (Equiv.ofInjective f hf).symm (Equiv.refl _))
  have hσ : ∀ i, σ.symm (.inl i) = f i := fun i => by
    simp only [σ, Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.symm_symm, Equiv.sumCompl_apply_inl, Equiv.ofInjective_apply]
  have h := sum_bernProd_split σ q (fun a _ => g a)
  have h1 : ∀ E : ι₁ → ZMod 2, (fun i => E (σ.symm (.inl i))) = E ∘ f := fun E => funext fun i => by
    simp only [Function.comp_apply, hσ]
  simp only [h1] at h
  rw [h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show (∑ b : {e // e ∉ Set.range f} → ZMod 2, bernProd q a * bernProd q b * g a) =
      bernProd q a * g a * ∑ b : {e // e ∉ Set.range f} → ZMod 2, bernProd q b by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring, sum_bernProd, mul_one]

/-- The probability of an event of the restricted errors. -/
theorem prob_comp_inj {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (q : ℝ) {f : ι₂ → ι₁}
    (hf : Function.Injective f) (A : (ι₂ → ZMod 2) → Prop) :
    prob (bernProd q) (fun E => A (E ∘ f)) = prob (bernProd q) A := by
  unfold prob
  have h := sum_bernProd_comp q hf (fun E' => if A E' then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  exact h

namespace S3Fam

variable (fam : S3Fam)

/-- **Hcov** ((R2) translation covariance of the stage-1 rule, validated by V2, made explicit; named hypothesis):
the stage-1 output of a block depends only on its window graph up to translation by whole blocks. For a code
embedded into a larger one (same `L`, `R`), a block whose contacts with the boundary of the smaller code are aligned
with the same boundaries of the larger code (`Emb.Congr`, so the two windows are clipped alike) has, on every
syndrome of the larger code, the push-forward of its own output on the pulled-back syndrome. -/
def Hcov : Prop :=
  ∀ (nx ny nx' ny' : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny) (hnx' : 1 ≤ nx') (hny' : 1 ≤ ny')
    (ι : S3Geom.Emb (fam.geom nx' ny' hnx' hny') (fam.geom nx ny hnx hny))
    (c : (fam.geom nx' ny' hnx' hny').Block), ι.Congr c →
    ∀ (D : (fam.geom nx ny hnx hny).V → ZMod 2) (e : (fam.geom nx' ny' hnx' hny').Ed),
      (fam.geom nx' ny' hnx' hny').owner e = c → S3Geom.isBulk e →
        (fam.stage1 nx ny hnx hny).F (ι.B c) D (ι.E e) = (fam.stage1 nx' ny' hnx' hny').F c (D ∘ ι.V) e

theorem refCol_cases {nx a : ℕ} (hnx : 5 ≤ nx) (ha : a < nx) :
    ((refCol nx a).val = 0 ∧ a = 0) ∨ ((refCol nx a).val = 1 ∧ a = 1) ∨
      ((refCol nx a).val = 4 ∧ a + 1 = nx) ∨ ((refCol nx a).val = 3 ∧ a + 2 = nx) ∨
        ((refCol nx a).val = 2 ∧ 2 ≤ a ∧ a + 3 ≤ nx) := by
  unfold refCol
  split_ifs
  all_goals simp_all
  all_goals omega

theorem distVB_bounds {G : S3Geom} {v : G.V} {b : G.Block} (h : G.distVB v b ≤ G.R) :
    b.1.val * G.L ≤ v.1.val + G.R ∧ v.1.val + 1 ≤ b.1.val * G.L + G.L + G.R ∧
      b.2.val * G.L ≤ v.2.val + G.R ∧ v.2.val + 1 ≤ b.2.val * G.L + G.L + G.R := by
  have := G.hL
  simp only [S3Geom.distVB, dist1, max_le_iff] at h
  omega

theorem blockDist_le_one {G : S3Geom} {b c : G.Block} (h : G.blockDist b c ≤ 1) :
    b.1.val ≤ c.1.val + 1 ∧ c.1.val ≤ b.1.val + 1 ∧ b.2.val ≤ c.2.val + 1 ∧ c.2.val ≤ b.2.val + 1 := by
  simp only [S3Geom.blockDist, ndist, max_le_iff] at h
  omega

theorem mul_le_add_of_le_succ {x y L : ℕ} (h : x ≤ y + 1) : x * L ≤ y * L + L := by
  have := Nat.mul_le_mul_right L h
  rwa [Nat.succ_mul] at this

/-- Coordinates of a check whose block column lies in `[a, a + 4]`. -/
theorem coord_recover {x L a : ℕ} (hL : 0 < L) (h1 : a ≤ x / L) (h2 : x / L ≤ a + 4) :
    L * a ≤ x ∧ x - L * a < 5 * L := by
  have e1 := Nat.mul_div_le x L
  have e2 := Nat.lt_mul_div_succ x hL
  have e3 := Nat.mul_le_mul_left L h1
  have e4 : L * (x / L + 1) ≤ L * (a + 5) := Nat.mul_le_mul_left L (by omega)
  have e5 : L * (a + 5) = L * a + 5 * L := by ring
  omega

/-- **Block types from translation covariance**: for `R < L`, `Hcov` implies `Htype`. -/
theorem htype_of_hcov (hRL : fam.R < fam.L) (hcov : fam.Hcov) (q : ℝ) : fam.Htype q := by
  intro nx ny hnx hny c hc
  have hL1 : 1 ≤ fam.L := fam.hL
  have hcol : c.1.val < nx := c.1.isLt
  have hrow : c.2.val < ny := c.2.isLt
  obtain ⟨hrow2, hrow3⟩ := hc
  change 2 ≤ c.2.val at hrow2
  change c.2.val + 3 ≤ ny at hrow3
  have hcases := refCol_cases hnx hcol
  have ht_le : (refCol nx c.1.val).val ≤ c.1.val := by rcases hcases with h | h | h | h | h <;> omega
  have hw : 5 + (c.1.val - (refCol nx c.1.val).val) ≤ nx := by rcases hcases with h | h | h | h | h <;> omega
  let ι : S3Geom.Emb fam.refGeom (fam.geom nx ny (by omega) (by omega)) :=
    ⟨c.1.val - (refCol nx c.1.val).val, c.2.val - 2, rfl, rfl, hw, by show 5 + (c.2.val - 2) ≤ ny; omega⟩
  have hB : ι.B (fam.refBlock (refCol nx c.1.val)) = c := by
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show (refCol nx c.1.val).val + (c.1.val - (refCol nx c.1.val).val) = c.1.val
      omega
    · show 2 + (c.2.val - 2) = c.2.val
      omega
  -- arithmetic facts, with `t` the reference column
  obtain ⟨t, ht⟩ : ∃ t, (refCol nx c.1.val).val = t := ⟨_, rfl⟩
  rw [ht] at hcases ht_le
  have ha : ι.a = c.1.val - t := by
    show c.1.val - (refCol nx c.1.val).val = _
    rw [ht]
  have hb : ι.b = c.2.val - 2 := rfl
  have hLa : fam.L * ι.a + t * fam.L = c.1.val * fam.L := by
    rw [ha, mul_comm, ← Nat.add_mul, Nat.sub_add_cancel ht_le]
  have hLb : fam.L * ι.b + 2 * fam.L = c.2.val * fam.L := by
    rw [hb, mul_comm, ← Nat.add_mul, Nat.sub_add_cancel hrow2]
  have hRa : 3 ≤ t → ι.a + 5 = nx := fun h3 => by
    rw [ha]
    rcases hcases with h | h | h | h | h <;> omega
  have hLR : 3 ≤ t → fam.L * ι.a + 5 * fam.L = nx * fam.L := fun h3 => by
    rw [mul_comm, ← Nat.add_mul, hRa h3]
  have hLa0 : t ≤ 1 → ι.a = 0 := fun h1 => by
    rw [ha]
    rcases hcases with h | h | h | h | h <;> omega
  have hbh : ι.b + 5 ≤ ny := by rw [hb]; omega
  have hLbh : fam.L * ι.b + 5 * fam.L ≤ ny * fam.L := by
    rw [mul_comm, ← Nat.add_mul]
    exact Nat.mul_le_mul_right _ hbh
  have ht4 : t ≤ 4 := by rcases hcases with h | h | h | h | h <;> omega
  have hwG : nx * fam.L - 1 + 1 = nx * fam.L := (fam.geom nx ny (by omega) (by omega)).w_succ
  have hhG : ny * fam.L - 1 + 1 = ny * fam.L := (fam.geom nx ny (by omega) (by omega)).h_succ
  have hRL' : fam.R + 1 ≤ fam.L := hRL
  -- congruence of the blocks of `N_1(c')`
  have hcongr : ∀ b : fam.refGeom.Block, fam.refGeom.blockDist b (fam.refBlock (refCol nx c.1.val)) ≤ 1 →
      ι.Congr b := by
    intro b hb'
    obtain ⟨h1, h2, h3, h4⟩ := blockDist_le_one hb'
    have e1 : (fam.refBlock (refCol nx c.1.val)).1.val = t := ht
    have e2 : (fam.refBlock (refCol nx c.1.val)).2.val = 2 := rfl
    rw [e1] at h1 h2
    rw [e2] at h3 h4
    refine ⟨fun h0 => hLa0 (by omega), fun h5 => ?_, fun h0 => ?_, fun h5 => ?_⟩
    · change b.1.val + 1 = 5 at h5
      change 5 + ι.a = nx
      have := hRa (by omega)
      omega
    · omega
    · change b.2.val + 1 = 5 at h5
      omega
  have hLpos : 0 < fam.L := by omega
  have hLa0' : t ≤ 1 → fam.L * ι.a = 0 := fun h => by rw [hLa0 h, mul_zero]
  -- the windows of `N_1(c)` lie in the embedded region
  have hK1 : ∀ v : (fam.geom nx ny (by omega) (by omega)).V,
      (∃ b : (fam.geom nx ny (by omega) (by omega)).Block,
        (fam.geom nx ny (by omega) (by omega)).blockDist b (ι.B (fam.refBlock (refCol nx c.1.val))) ≤ 1 ∧
        (fam.geom nx ny (by omega) (by omega)).distVB v b ≤ (fam.geom nx ny (by omega) (by omega)).R) →
      ∃ v', ι.V v' = v := by
    rintro v ⟨b, hb', hd⟩
    rw [hB] at hb'
    have hvb := S3Geom.blockDist_le_one_of_distVB (le_trans hd (le_of_lt hRL))
    obtain ⟨h1, h2, h3, h4⟩ := blockDist_le_one hb'
    obtain ⟨g1, g2, g3, g4⟩ := blockDist_le_one hvb
    have gx : ((fam.geom nx ny (by omega) (by omega)).blockOf v).1.val = v.1.val / fam.L := rfl
    have gy : ((fam.geom nx ny (by omega) (by omega)).blockOf v).2.val = v.2.val / fam.L := rfl
    have gxl : ((fam.geom nx ny (by omega) (by omega)).blockOf v).1.val < nx :=
      ((fam.geom nx ny (by omega) (by omega)).blockOf v).1.isLt
    rw [gx] at g1 g2 gxl
    rw [gy] at g3 g4
    have hc1 : ι.a ≤ v.1.val / fam.L ∧ v.1.val / fam.L ≤ ι.a + 4 := by
      rw [ha]
      rcases hcases with h | h | h | h | h <;> omega
    have hc2 : ι.b ≤ v.2.val / fam.L ∧ v.2.val / fam.L ≤ ι.b + 4 := by
      rw [hb]
      omega
    obtain ⟨x1, x2⟩ := coord_recover hLpos hc1.1 hc1.2
    obtain ⟨y1, y2⟩ := coord_recover hLpos hc2.1 hc2.2
    refine ⟨(⟨v.1.val - fam.L * ι.a, by show _ < 5 * fam.L - 1 + 1; omega⟩,
      ⟨v.2.val - fam.L * ι.b, by show _ < 5 * fam.L - 1 + 1; omega⟩), Prod.ext (Fin.ext ?_) (Fin.ext ?_)⟩
    · show v.1.val - fam.L * ι.a + fam.L * ι.a = v.1.val
      omega
    · show v.2.val - fam.L * ι.b + fam.L * ι.b = v.2.val
      omega
  -- the window checks of `N_1(c')` in the reference code
  have hW : ∀ v' : fam.refGeom.V, Stage1.InW (fam.refBlock (refCol nx c.1.val)) v' →
      1 ≤ v'.2.val ∧ v'.2.val + 2 ≤ 5 * fam.L ∧ (2 ≤ t → 1 ≤ v'.1.val) ∧ (t ≤ 2 → v'.1.val + 2 ≤ 5 * fam.L) := by
    rintro v' ⟨b', hb', hd⟩
    obtain ⟨h1, h2, h3, h4⟩ := blockDist_le_one hb'
    have e1 : (fam.refBlock (refCol nx c.1.val)).1.val = t := ht
    have e2 : (fam.refBlock (refCol nx c.1.val)).2.val = 2 := rfl
    rw [e1] at h1 h2
    rw [e2] at h3 h4
    obtain ⟨d1, d2, d3, d4⟩ := distVB_bounds hd
    change b'.1.val * fam.L ≤ v'.1.val + fam.R at d1
    change v'.1.val + 1 ≤ b'.1.val * fam.L + fam.L + fam.R at d2
    change b'.2.val * fam.L ≤ v'.2.val + fam.R at d3
    change v'.2.val + 1 ≤ b'.2.val * fam.L + fam.L + fam.R at d4
    have p1 : 1 * fam.L ≤ b'.2.val * fam.L := Nat.mul_le_mul_right _ (by omega)
    have p2 : b'.2.val * fam.L ≤ 3 * fam.L := Nat.mul_le_mul_right _ (by omega)
    have p3 := mul_le_add_of_le_succ (L := fam.L) h2
    have p4 := mul_le_add_of_le_succ (L := fam.L) h1
    refine ⟨by omega, by omega, fun h => ?_, fun h => ?_⟩
    · have : 2 * fam.L ≤ t * fam.L := Nat.mul_le_mul_right _ h
      omega
    · have : t * fam.L ≤ 2 * fam.L := Nat.mul_le_mul_right _ h
      omega
  have hK4 : ∀ v', Stage1.InW (fam.refBlock (refCol nx c.1.val)) v' →
      ∀ e' : fam.refGeom.Ed, v' ∈ e'.ends → S3Geom.isBulk e' := by
    intro v' hv e' he'
    obtain ⟨r1, r2, -, -⟩ := hW v' hv
    rcases e' with ⟨x, y⟩ | ⟨x, y⟩ | x | x
    · trivial
    · trivial
    · simp only [PEdge.ends, Finset.mem_singleton] at he'
      rw [he'] at r1
      simp at r1
    · simp only [PEdge.ends, Finset.mem_singleton] at he'
      rw [he'] at r2
      simp only [Fin.val_last] at r2
      change 5 * fam.L - 1 + 2 ≤ 5 * fam.L at r2
      omega
  have hK3 : ∀ v', Stage1.InW (fam.refBlock (refCol nx c.1.val)) v' →
      ∀ e, ι.V v' ∈ PEdge.ends e → ∃ e', S3Geom.isBulk e' ∧ ι.E e' = e := by
    intro v' hv e he
    obtain ⟨r1, r2, c1, c2⟩ := hW v' hv
    have hv1 : v'.1.val < 5 * fam.L := by have := v'.1.isLt; change _ < 5 * fam.L - 1 + 1 at this; omega
    have hv2 : v'.2.val < 5 * fam.L := by have := v'.2.isLt; change _ < 5 * fam.L - 1 + 1 at this; omega
    rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x
    · have hx : x.val < nx * fam.L - 1 := x.isLt
      simp only [PEdge.ends, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff,
        S3Geom.Emb.V_fst, S3Geom.Emb.V_snd, Fin.val_castSucc, Fin.val_succ] at he
      change (v'.1.val + fam.L * ι.a = x.val ∧ v'.2.val + fam.L * ι.b = y.val) ∨
        (v'.1.val + fam.L * ι.a = x.val + 1 ∧ v'.2.val + fam.L * ι.b = y.val) at he
      rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have hlt : v'.1.val < 5 * fam.L - 1 := by
          by_cases h3 : 3 ≤ t
          · have := hLR h3
            omega
          · have := c2 (by omega)
            omega
        refine ⟨.hor ⟨v'.1.val, hlt⟩ ⟨v'.2.val, by change _ < 5 * fam.L - 1 + 1; omega⟩, trivial, ?_⟩
        simp only [S3Geom.Emb.E, PEdge.hor.injEq, Fin.ext_iff]
        exact ⟨e1, e2⟩
      · have hge : 1 ≤ v'.1.val := by
          by_cases h2 : 2 ≤ t
          · exact c1 h2
          · have := hLa0' (by omega)
            omega
        refine ⟨.hor ⟨v'.1.val - 1, by change _ < 5 * fam.L - 1; omega⟩
          ⟨v'.2.val, by change _ < 5 * fam.L - 1 + 1; omega⟩, trivial, ?_⟩
        simp only [S3Geom.Emb.E, PEdge.hor.injEq, Fin.ext_iff]
        constructor <;> omega
    · simp only [PEdge.ends, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff,
        S3Geom.Emb.V_fst, S3Geom.Emb.V_snd, Fin.val_castSucc, Fin.val_succ] at he
      change (v'.1.val + fam.L * ι.a = x.val ∧ v'.2.val + fam.L * ι.b = y.val) ∨
        (v'.1.val + fam.L * ι.a = x.val ∧ v'.2.val + fam.L * ι.b = y.val + 1) at he
      rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · refine ⟨.ver ⟨v'.1.val, by change _ < 5 * fam.L - 1 + 1; omega⟩
          ⟨v'.2.val, by change _ < 5 * fam.L - 1; omega⟩, trivial, ?_⟩
        simp only [S3Geom.Emb.E, PEdge.ver.injEq, Fin.ext_iff]
        exact ⟨e1, e2⟩
      · refine ⟨.ver ⟨v'.1.val, by change _ < 5 * fam.L - 1 + 1; omega⟩
          ⟨v'.2.val - 1, by change _ < 5 * fam.L - 1; omega⟩, trivial, ?_⟩
        simp only [S3Geom.Emb.E, PEdge.ver.injEq, Fin.ext_iff]
        constructor <;> omega
    · simp only [PEdge.ends, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff, S3Geom.Emb.V_snd] at he
      have := he.2
      simp only [Fin.val_zero] at this
      omega
    · simp only [PEdge.ends, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff, S3Geom.Emb.V_snd,
        Fin.val_last] at he
      have := he.2
      change v'.2.val + fam.L * ι.b = ny * fam.L - 1 at this
      omega
  -- covariance on `N_1(c')`
  have hcovOn : fam.refStage1.CovOn (fam.stage1 nx ny (by omega) (by omega)) ι
      (fun b => fam.refGeom.blockDist b (fam.refBlock (refCol nx c.1.val)) ≤ 1) :=
    fun b hb' D e he hbulk => hcov nx ny 5 5 _ _ (by norm_num) (by norm_num) ι b (hcongr b hb') D e he hbulk
  refine (prob_congr _ (fun E => ?_)).trans (prob_comp_inj q ι.E_inj _)
  have key := Stage1.bad_iff_of_emb hcovOn hK1 hK3 hK4 E
  rw [hB] at key
  exact key

end S3Fam

end QECML
