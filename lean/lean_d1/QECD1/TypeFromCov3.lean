import QECD1.Covariance3

/-!
# Block types from translation covariance, on the 3D code

The 3D analogue of the 2D `S3/TypeFromCov`.

* `prob_comp_inj`: the probability of an event of `X ∘ f`, for an injective map of edges `f`, is the probability of
  the event on the smaller set of edges (the product measure pushed forward along a restriction).
* `Emb3.edge_image_of_ends`: a bulk edge whose ends are images is the image of a bulk edge.
* `Hcov3` (named hypothesis on the stage-1 rules; (R2) translation covariance, validated by V2, made explicit): for a
  code embedded into a larger one, a block whose contacts with the boundary of the smaller code are aligned with the
  same boundaries of the larger code (`Emb3.Congr`) has, on every syndrome of the larger code, the push-forward of
  its own output on the pulled-back syndrome.
* `htype3_of_hcov3`: `Hcov3` implies `Htype3`. A block `c` of type `(i, j)` is the image of the reference block
  `(i, j, 2)` under the embedding of the `5 × 5 × 5` reference code at offset `c - (i, j, 2)`. Since `R = 34 < L = 35`,
  the windows of `N_1(c)` lie inside the image, their checks see no half-edge, and the blocks of `N_1` of the
  reference block are congruent. So the bad events correspond (`bad_iff_of_emb`) and have the same probability
  (`prob_comp_inj`).
-/

open Finset Classical

namespace QECD1

/-- **Restriction along an injective map**: the probability of an event of the restricted configuration `X ∘ f` is its
probability on the smaller set of edges. -/
theorem prob_comp_inj {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (p : ℝ)
    {f : ι₂ → ι₁} (hf : Function.Injective f) (A : (ι₂ → Bool) → Prop) :
    prob p (fun X : ι₁ → Bool => A (X ∘ f)) = prob p A := by
  let S : Finset ι₁ := Finset.univ.image f
  let g : ι₂ ≃ {e // e ∈ S} := (Equiv.ofInjective f hf).trans (Equiv.subtypeEquivRight fun e => by simp [S])
  have hcomp : ∀ u v, ((splitE S).symm (u, v)) ∘ f = u ∘ g := by
    intro u v
    funext e'
    simp only [Function.comp_apply]
    rw [splitE_symm_in S u v (Finset.mem_image_of_mem f (Finset.mem_univ e'))]
    rfl
  have hpw : ∀ u : {e // e ∈ S} → Bool, pwS p u = pw p (u ∘ g) := fun u =>
    (Fintype.prod_equiv g (fun e' => if u (g e') then p else 1 - p) (fun s => if u s then p else 1 - p)
      fun _ => rfl).symm
  calc prob p (fun X : ι₁ → Bool => A (X ∘ f))
      = ∑ u : {e // e ∈ S} → Bool, (if A (u ∘ g) then pwS p u else 0) := by
        unfold prob
        rw [sum_split S]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hA : A (u ∘ g)
        · simp only [hcomp, if_pos hA, pw_split]
          rw [← Finset.mul_sum, sum_pwS, mul_one]
        · simp only [hcomp, if_neg hA, Finset.sum_const_zero]
    _ = ∑ X' : ι₂ → Bool, (if A X' then pw p X' else 0) := by
        refine Fintype.sum_equiv (Equiv.arrowCongr g.symm (Equiv.refl Bool)) _ _ fun u => ?_
        have hu : (Equiv.arrowCongr g.symm (Equiv.refl Bool)) u = u ∘ g := by
          funext e'
          rfl
        rw [hu, hpw u]
    _ = prob p A := rfl

variable {T' w' h' T w h : ℕ}

/-- A bulk edge whose ends are all images is the image of a bulk edge. -/
theorem Emb3.edge_image_of_ends (ι : Emb3 T' w' h' T w h) {e : PEdge3 T w h} (he : ¬ e.isHalf)
    (hends : ∀ u ∈ e.ends, ∃ u', ι.V u' = u) : ∃ e', ¬ e'.isHalf ∧ ι.E e' = e := by
  cases e with
  | hor t x y =>
    obtain ⟨u1, hu1⟩ := hends (t, x.castSucc, y) (by simp [PEdge3.ends])
    obtain ⟨u2, hu2⟩ := hends (t, x.succ, y) (by simp [PEdge3.ends])
    have e1 := congrArg (fun u : PVert3 T w h => u.1.val) hu1
    have e2 := congrArg (fun u : PVert3 T w h => u.2.1.val) hu1
    have e3 := congrArg (fun u : PVert3 T w h => u.2.2.val) hu1
    have f2 := congrArg (fun u : PVert3 T w h => u.2.1.val) hu2
    simp only [Emb3.V_t, Emb3.V_x, Emb3.V_y, Fin.val_castSucc, Fin.val_succ] at e1 e2 e3 f2
    have hu2x := u2.2.1.isLt
    refine ⟨.hor u1.1 ⟨u1.2.1.val, by omega⟩ u1.2.2, id, ?_⟩
    simp only [Emb3.E, PEdge3.hor.injEq]
    exact ⟨Fin.ext (by simp only; omega), Fin.ext (by simp only; omega), Fin.ext (by simp only; omega)⟩
  | ver t x y =>
    obtain ⟨u1, hu1⟩ := hends (t, x, y.castSucc) (by simp [PEdge3.ends])
    obtain ⟨u2, hu2⟩ := hends (t, x, y.succ) (by simp [PEdge3.ends])
    have e1 := congrArg (fun u : PVert3 T w h => u.1.val) hu1
    have e2 := congrArg (fun u : PVert3 T w h => u.2.1.val) hu1
    have e3 := congrArg (fun u : PVert3 T w h => u.2.2.val) hu1
    have f3 := congrArg (fun u : PVert3 T w h => u.2.2.val) hu2
    simp only [Emb3.V_t, Emb3.V_x, Emb3.V_y, Fin.val_castSucc, Fin.val_succ] at e1 e2 e3 f3
    have hu2y := u2.2.2.isLt
    refine ⟨.ver u1.1 u1.2.1 ⟨u1.2.2.val, by omega⟩, id, ?_⟩
    simp only [Emb3.E, PEdge3.ver.injEq]
    exact ⟨Fin.ext (by simp only; omega), Fin.ext (by simp only; omega), Fin.ext (by simp only; omega)⟩
  | time t x y =>
    obtain ⟨u1, hu1⟩ := hends (t.castSucc, x, y) (by simp [PEdge3.ends])
    obtain ⟨u2, hu2⟩ := hends (t.succ, x, y) (by simp [PEdge3.ends])
    have e1 := congrArg (fun u : PVert3 T w h => u.1.val) hu1
    have e2 := congrArg (fun u : PVert3 T w h => u.2.1.val) hu1
    have e3 := congrArg (fun u : PVert3 T w h => u.2.2.val) hu1
    have f1 := congrArg (fun u : PVert3 T w h => u.1.val) hu2
    simp only [Emb3.V_t, Emb3.V_x, Emb3.V_y, Fin.val_castSucc, Fin.val_succ] at e1 e2 e3 f1
    have hu2t := u2.1.isLt
    refine ⟨.time ⟨u1.1.val, by omega⟩ u1.2.1 u1.2.2, id, ?_⟩
    simp only [Emb3.E, PEdge3.time.injEq]
    exact ⟨Fin.ext (by simp only; omega), Fin.ext (by simp only; omega), Fin.ext (by simp only; omega)⟩
  | bot t x => exact absurd trivial he
  | top t x => exact absurd trivial he

/-- The checks of a window of a block of `N_1(c)`: within `[35 c - 69, 35 c + 103]` in each coordinate. -/
theorem win_coords {b c p : V3} (hb : dist3 b c ≤ 1) (hw : InWin b p) :
    c.1 * 35 - 69 ≤ p.1 ∧ p.1 ≤ c.1 * 35 + 103 ∧ c.2.1 * 35 - 69 ≤ p.2.1 ∧ p.2.1 ≤ c.2.1 * 35 + 103 ∧
      c.2.2 * 35 - 69 ≤ p.2.2 ∧ p.2.2 ≤ c.2.2 * 35 + 103 := by
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  simp only [coord] at h0 h1 h2
  simp only [dist3, linf, Prod.fst_sub, Prod.snd_sub, max_le_iff] at hb
  omega

theorem refCol_cases {n a : ℕ} (hn : 5 ≤ n) (ha : a < n) :
    ((refCol n a).val = 0 ∧ a = 0) ∨ ((refCol n a).val = 1 ∧ a = 1) ∨ ((refCol n a).val = 4 ∧ a + 1 = n) ∨
      ((refCol n a).val = 3 ∧ a + 2 = n) ∨ ((refCol n a).val = 2 ∧ 2 ≤ a ∧ a + 3 ≤ n) := by
  unfold refCol
  split_ifs
  all_goals simp_all
  all_goals omega

namespace S3Fam3

variable (fam : S3Fam3)

/-- **Hcov3** ((R2) translation covariance of the stage-1 rules, made explicit; named hypothesis). -/
def Hcov3 : Prop :=
  ∀ (nt nx ny nt' nx' ny' : ℕ), 1 ≤ nt → 1 ≤ nx → 1 ≤ ny → 1 ≤ nt' → 1 ≤ nx' → 1 ≤ ny' →
    ∀ (ι : Emb3 (nt' * 35 - 1) (nx' * 35 - 1) (ny' * 35 - 1) (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1)) (c : V3),
      ι.Congr c → ∀ (D : PVert3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1) → ZMod 2)
        (e : PEdge3 (nt' * 35 - 1) (nx' * 35 - 1) (ny' * 35 - 1)), owner3 e = c → ¬ e.isHalf →
          (fam.stage1 nt nx ny).F (ι.B c) D (ι.E e) = (fam.stage1 nt' nx' ny').F c (D ∘ ι.V) e

/-- **Block types from translation covariance**: `Hcov3` implies `Htype3`. -/
theorem htype3_of_hcov3 (hcov : fam.Hcov3) (p : ℝ) : fam.Htype3 p := by
  intro nt nx ny hnt hnx hny c hc hnd
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hc
  simp only [declared3, not_or, not_lt, not_le] at hnd
  obtain ⟨ct, hct⟩ : ∃ ct : ℕ, c.1 = ct := ⟨c.1.toNat, by omega⟩
  obtain ⟨cx, hcx⟩ : ∃ cx : ℕ, c.2.1 = cx := ⟨c.2.1.toNat, by omega⟩
  obtain ⟨cy, hcy⟩ : ∃ cy : ℕ, c.2.2 = cy := ⟨c.2.2.toNat, by omega⟩
  have hct' : c.1.toNat = ct := by omega
  have hcx' : c.2.1.toNat = cx := by omega
  rw [hct', hcx']
  have htc := refCol_cases hnt (show ct < nt by omega)
  have hxc := refCol_cases hnx (show cx < nx by omega)
  obtain ⟨ti, hti⟩ : ∃ ti : Fin 5, refCol nt ct = ti := ⟨_, rfl⟩
  obtain ⟨xi, hxi⟩ : ∃ xi : Fin 5, refCol nx cx = xi := ⟨_, rfl⟩
  rw [hti] at htc ⊢
  rw [hxi] at hxc ⊢
  have hy2 : 2 ≤ cy := by omega
  have hy3 : cy + 3 ≤ ny := by omega
  -- the embedding of the reference code at offset `c - (ti, xi, 2)`
  obtain ⟨ι, hιa, hιb, hιd⟩ : ∃ ι : Emb3 (5 * 35 - 1) (5 * 35 - 1) (5 * 35 - 1) (nt * 35 - 1) (nx * 35 - 1)
      (ny * 35 - 1), ι.a = ct - ti.val ∧ ι.b = cx - xi.val ∧ ι.d = cy - 2 :=
    ⟨⟨ct - ti.val, cx - xi.val, cy - 2, by rcases htc with h | h | h | h | h <;> omega,
      by rcases hxc with h | h | h | h | h <;> omega, by omega⟩, rfl, rfl, rfl⟩
  have hB : ι.B (refBlock ti xi) = c := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show ((ti : ℕ) : ℤ) + (ι.a : ℤ) = c.1
      rw [hιa]
      rcases htc with h | h | h | h | h <;> omega
    · show ((xi : ℕ) : ℤ) + (ι.b : ℤ) = c.2.1
      rw [hιb]
      rcases hxc with h | h | h | h | h <;> omega
    · show (2 : ℤ) + (ι.d : ℤ) = c.2.2
      rw [hιd]
      omega
  -- the blocks of `N_1` of the reference block are congruent
  have hcongr : ∀ b : V3, dist3 b (refBlock ti xi) ≤ 1 → ι.Congr b := by
    intro b hb
    simp only [dist3, linf, refBlock, Prod.fst_sub, Prod.snd_sub, max_le_iff] at hb
    refine ⟨fun h0 => ?_, fun h4 => ?_, fun h0 => ?_, fun h4 => ?_, fun h0 => ?_, fun h4 => ?_⟩
    · rw [hιa]
      rcases htc with h | h | h | h | h <;> omega
    · rw [hιa]
      rcases htc with h | h | h | h | h <;> omega
    · rw [hιb]
      rcases hxc with h | h | h | h | h <;> omega
    · rw [hιb]
      rcases hxc with h | h | h | h | h <;> omega
    · omega
    · omega
  -- the checks in the windows of `N_1(c)` are images
  have hK1 : ∀ v : PVert3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1),
      (∃ b, dist3 b (ι.B (refBlock ti xi)) ≤ 1 ∧ InWin b v.toV3) → ∃ v', ι.V v' = v := by
    rintro ⟨t, x, y⟩ ⟨b, hb, hw⟩
    rw [hB] at hb
    have hwc := win_coords hb hw
    simp only [PVert3.toV3] at hwc
    have ht := t.isLt
    have hx := x.isLt
    have hy := y.isLt
    have hta : 35 * ι.a ≤ t.val ∧ t.val - 35 * ι.a < 5 * 35 - 1 + 1 := by
      rw [hιa]
      rcases htc with h | h | h | h | h <;> omega
    have hxa : 35 * ι.b ≤ x.val ∧ x.val - 35 * ι.b < 5 * 35 - 1 + 1 := by
      rw [hιb]
      rcases hxc with h | h | h | h | h <;> omega
    have hya : 35 * ι.d ≤ y.val ∧ y.val - 35 * ι.d < 5 * 35 - 1 + 1 := by
      rw [hιd]
      omega
    refine ⟨(⟨t.val - 35 * ι.a, hta.2⟩, ⟨x.val - 35 * ι.b, hxa.2⟩, ⟨y.val - 35 * ι.d, hya.2⟩), ?_⟩
    exact Prod.ext (Fin.ext (by simp only [Emb3.V_t]; omega))
      (Prod.ext (Fin.ext (by simp only [Emb3.V_x]; omega)) (Fin.ext (by simp only [Emb3.V_y]; omega)))
  -- window checks of the reference code: coordinates
  have hwin : ∀ v' : PVert3 (5 * 35 - 1) (5 * 35 - 1) (5 * 35 - 1), InW3 (refBlock ti xi) v' →
      (ti.val : ℤ) * 35 - 69 ≤ (v'.1.val : ℤ) ∧ (v'.1.val : ℤ) ≤ (ti.val : ℤ) * 35 + 103 ∧
        (xi.val : ℤ) * 35 - 69 ≤ (v'.2.1.val : ℤ) ∧ (v'.2.1.val : ℤ) ≤ (xi.val : ℤ) * 35 + 103 ∧
          1 ≤ v'.2.2.val ∧ v'.2.2.val ≤ 173 := by
    rintro v' ⟨b, hb, hw⟩
    have hwc := win_coords hb hw
    simp only [refBlock, PVert3.toV3] at hwc
    omega
  -- the edges at window checks of the reference code are bulk
  have hK4 : ∀ v', InW3 (refBlock ti xi) v' → ∀ e' : PEdge3 (5 * 35 - 1) (5 * 35 - 1) (5 * 35 - 1),
      v' ∈ e'.ends → ¬ e'.isHalf := by
    intro v' hv' e' he'
    have hc' := hwin v' hv'
    cases e' with
    | hor t x y => exact id
    | ver t x y => exact id
    | time t x y => exact id
    | bot t x =>
      simp only [PEdge3.ends, Finset.mem_singleton] at he'
      subst he'
      simp at hc'
    | top t x =>
      simp only [PEdge3.ends, Finset.mem_singleton] at he'
      subst he'
      simp only [Fin.val_last] at hc'
      omega
  -- the edges at the images of window checks are images of bulk edges
  have hK3 : ∀ v', InW3 (refBlock ti xi) v' → ∀ e : PEdge3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1),
      ι.V v' ∈ e.ends → ∃ e', ¬ e'.isHalf ∧ ι.E e' = e := by
    intro v' hv' e he
    have hc' := hwin v' hv'
    have hv1 := v'.1.isLt
    have hv2 := v'.2.1.isLt
    have hends : ∀ u ∈ e.ends, ∃ u', ι.V u' = u := by
      intro u hu
      have hadj := ends_adjacent e he hu
      obtain ⟨t, x, y⟩ := u
      have ht := t.isLt
      have hx := x.isLt
      have hy := y.isLt
      simp only [linf, PVert3.toV3, Prod.fst_sub, Prod.snd_sub, max_le_iff, Emb3.V_t, Emb3.V_x, Emb3.V_y]
        at hadj
      have hta : 35 * ι.a ≤ t.val ∧ t.val - 35 * ι.a < 5 * 35 - 1 + 1 := by
        rw [hιa] at hadj ⊢
        rcases htc with h | h | h | h | h <;> omega
      have hxa : 35 * ι.b ≤ x.val ∧ x.val - 35 * ι.b < 5 * 35 - 1 + 1 := by
        rw [hιb] at hadj ⊢
        rcases hxc with h | h | h | h | h <;> omega
      have hya : 35 * ι.d ≤ y.val ∧ y.val - 35 * ι.d < 5 * 35 - 1 + 1 := by
        rw [hιd] at hadj ⊢
        omega
      refine ⟨(⟨t.val - 35 * ι.a, hta.2⟩, ⟨x.val - 35 * ι.b, hxa.2⟩, ⟨y.val - 35 * ι.d, hya.2⟩), ?_⟩
      exact Prod.ext (Fin.ext (by simp only [Emb3.V_t]; omega))
        (Prod.ext (Fin.ext (by simp only [Emb3.V_x]; omega)) (Fin.ext (by simp only [Emb3.V_y]; omega)))
    have hbulk : ¬ e.isHalf := by
      cases e with
      | hor t x y => exact id
      | ver t x y => exact id
      | time t x y => exact id
      | bot t x =>
        simp only [PEdge3.ends, Finset.mem_singleton] at he
        have := congrArg (fun u : PVert3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1) => u.2.2.val) he
        simp only [Emb3.V_y, Fin.val_zero] at this
        omega
      | top t x =>
        simp only [PEdge3.ends, Finset.mem_singleton] at he
        have := congrArg (fun u : PVert3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1) => u.2.2.val) he
        simp only [Emb3.V_y, Fin.val_last] at this
        rw [hιd] at this
        omega
    exact ι.edge_image_of_ends hbulk hends
  -- covariance on `N_1` of the reference block
  have hcovOn : (fam.stage1 5 5 5).CovOn (fam.stage1 nt nx ny) ι (fun b => dist3 b (refBlock ti xi) ≤ 1) :=
    fun b hb D e he hbulk => hcov nt nx ny 5 5 5 (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
      (by norm_num) ι b (hcongr b hb) D e he hbulk
  have hbad : ∀ X : PEdge3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1) → Bool,
      (fam.stage1 nt nx ny).bad (toZ2 X) c ↔ (fam.stage1 5 5 5).bad (toZ2 (X ∘ ι.E)) (refBlock ti xi) := by
    intro X
    rw [← hB]
    exact Stage13.bad_iff_of_emb hcovOn hK1 hK3 hK4 (toZ2 X)
  rw [prob_congr hbad]
  exact prob_comp_inj p ι.E_inj (fun X' => (fam.stage1 5 5 5).bad (toZ2 X') (refBlock ti xi))

/-- **(H_eps) from covariance and the statistical input**: `Hcov3` and `Hstat3` give (H_eps) on every undeclared
block, hence the bound for a family's event (`famEvent_prob_le_types`). -/
theorem famEvent_prob_le_cov {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hcov : fam.Hcov3) (hstat : fam.Hstat3 p ε)
    {nt nx ny : ℕ} (hnt : 5 ≤ nt) (hnx : 5 ≤ nx) (hny : 5 ≤ ny) (reach0 reach1 : Finset V3 → Prop) (e x : V3) :
    ∃ K : Finset Skel3, (∀ k ∈ K, k.1 = e ∧ SkelOK k) ∧
      prob p (fun X => (fam.stage1 nt nx ny).FamEvent reach0 reach1 ny e x (toZ2 X)) ≤
        ∑ k ∈ K, ε ^ (keyBlocks e k.2.2).length :=
  fam.famEvent_prob_le_types hp0 hp1 (fam.htype3_of_hcov3 hcov p) hstat hnt hnx hny reach0 reach1 e x

end S3Fam3

end QECD1
