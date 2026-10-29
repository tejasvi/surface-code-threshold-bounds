import QECD1.Embed3

/-!
# Covariance of stage-1 rules along an embedding, and the transport of the bad event (3D)

The 3D analogue of the 2D `S3/Covariance`.

* `Emb3.Congr`: a block of the small code is congruent with its image if every boundary of the small code it touches
  is aligned with the same boundary of the large code (then the two windows are clipped alike).
* `Stage13.CovOn`: covariance of two stage-1 rules along an embedding on a set of blocks: the output of the image
  block on a syndrome is the push-forward of the output of the block on the pulled-back syndrome.
* `InW3 c₀`: the checks in a window of a block of `N_1(c₀)`.
* `bad_iff_of_emb`: suppose the checks in the windows of `N_1(ι c₀)` are images (`hK1`), the edges at the images of
  window checks are images of bulk edges (`hK3`), the edges at window checks are bulk (`hK4`), and the rules are
  covariant on `N_1(c₀)`. Then `bad E (ι c₀) ↔ bad (E ∘ ι) c₀`. The flagged part compares the residuals at the checks
  of `c₀` (`psyn3_Fcfg_V`); the long part maps the walks of `E + C_0` inside `{distVB · c₀ < 35}` step by step
  (`fadj_V_iff`).
-/

open Finset

namespace QECD1

variable {T' w' h' T w h : ℕ}

namespace Emb3

variable (ι : Emb3 T' w' h' T w h)

/-- Congruence of a block of the small code with its image: each boundary of the small code touched by the block is
aligned with the same boundary of the large code. -/
def Congr (c : V3) : Prop :=
  (c.1 = 0 → ι.a = 0) ∧ (c.1 * 35 + 35 = (T' : ℤ) + 1 → T' + 35 * ι.a = T) ∧
    (c.2.1 = 0 → ι.b = 0) ∧ (c.2.1 * 35 + 35 = (w' : ℤ) + 1 → w' + 35 * ι.b = w) ∧
    (c.2.2 = 0 → ι.d = 0) ∧ (c.2.2 * 35 + 35 = (h' : ℤ) + 1 → h' + 35 * ι.d = h)

theorem B_inj : Function.Injective ι.B := fun c c' hc => by
  have h1 := congrArg (fun u : V3 => u.1) hc
  have h2 := congrArg (fun u : V3 => u.2.1) hc
  have h3 := congrArg (fun u : V3 => u.2.2) hc
  simp only [B] at h1 h2 h3
  exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))

end Emb3

/-- `v` lies in a window of a block of `N_1(c₀)`. -/
def InW3 (c0 : V3) (v : PVert3 T' w' h') : Prop := ∃ c, dist3 c c0 ≤ 1 ∧ InWin c v.toV3

theorem inW3_of_near {c0 : V3} {v : PVert3 T' w' h'} (hv : distVB v.toV3 c0 ≤ 34) : InW3 c0 v :=
  ⟨c0, by rw [dist3_self]; exact Nat.zero_le _, inWin_of_distVB hv⟩

namespace Stage13

/-- Covariance of the stage-1 rules `S'` (small code) and `S` (large code) along `ι`, for the blocks satisfying `P`. -/
def CovOn (S' : Stage13 T' w' h') (S : Stage13 T w h) (ι : Emb3 T' w' h' T w h) (P : V3 → Prop) : Prop :=
  ∀ c, P c → ∀ (D : PVert3 T w h → ZMod 2) (e : PEdge3 T' w' h'), owner3 e = c → ¬ e.isHalf →
    S.F (ι.B c) D (ι.E e) = S'.F c (D ∘ ι.V) e

section transport

variable {ι : Emb3 T' w' h' T w h} {c0 : V3}

/-- The edges at the image of a window check are the images of the (bulk) edges at it. -/
theorem filter_ends_V (hK3 : ∀ v', InW3 c0 v' → ∀ e : PEdge3 T w h, ι.V v' ∈ e.ends → ∃ e', ¬ e'.isHalf ∧ ι.E e' = e)
    (hK4 : ∀ v', InW3 c0 v' → ∀ e' : PEdge3 T' w' h', v' ∈ e'.ends → ¬ e'.isHalf) {v' : PVert3 T' w' h'}
    (hv : InW3 c0 v') :
    univ.filter (fun e : PEdge3 T w h => ι.V v' ∈ e.ends) =
      (univ.filter (fun e' : PEdge3 T' w' h' => v' ∈ e'.ends)).image ι.E := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro he
    obtain ⟨e', hb, rfl⟩ := hK3 v' hv e he
    exact ⟨e', (ι.mem_ends_E hb v').1 he, rfl⟩
  · rintro ⟨e', he', rfl⟩
    exact (ι.mem_ends_E (hK4 v' hv e' he') v').2 he'

/-- Syndromes at the image of a window check. -/
theorem sum_ends_V (hK3 : ∀ v', InW3 c0 v' → ∀ e : PEdge3 T w h, ι.V v' ∈ e.ends → ∃ e', ¬ e'.isHalf ∧ ι.E e' = e)
    (hK4 : ∀ v', InW3 c0 v' → ∀ e' : PEdge3 T' w' h', v' ∈ e'.ends → ¬ e'.isHalf) {v' : PVert3 T' w' h'}
    (hv : InW3 c0 v') (X : PEdge3 T w h → ZMod 2) (X' : PEdge3 T' w' h' → ZMod 2)
    (hX : ∀ e', v' ∈ e'.ends → X (ι.E e') = X' e') : psyn3 X (ι.V v') = psyn3 X' v' := by
  unfold psyn3
  rw [filter_ends_V hK3 hK4 hv, Finset.sum_image fun x _ y _ hxy => ι.E_inj hxy]
  exact Finset.sum_congr rfl fun e' he' => hX e' (Finset.mem_filter.1 he').2

end transport

section transport2

variable {S' : Stage13 T' w' h'} {S : Stage13 T w h} {ι : Emb3 T' w' h' T w h} {c0 : V3}
  (hcov : S'.CovOn S ι (fun c => dist3 c c0 ≤ 1))
  (hK1 : ∀ v : PVert3 T w h, (∃ c, dist3 c (ι.B c0) ≤ 1 ∧ InWin c v.toV3) → ∃ v', ι.V v' = v)
  (hK3 : ∀ v', InW3 c0 v' → ∀ e : PEdge3 T w h, ι.V v' ∈ e.ends → ∃ e', ¬ e'.isHalf ∧ ι.E e' = e)
  (hK4 : ∀ v', InW3 c0 v' → ∀ e' : PEdge3 T' w' h', v' ∈ e'.ends → ¬ e'.isHalf)
  (E : PEdge3 T w h → ZMod 2)

include hK3 hK4 in
/-- Syndromes agree at window checks. -/
theorem syn_V {v' : PVert3 T' w' h'} (hv : InW3 c0 v') : psyn3 E (ι.V v') = psyn3 (E ∘ ι.E) v' :=
  sum_ends_V hK3 hK4 hv E (E ∘ ι.E) fun _ _ => rfl

include hcov hK3 hK4 in
/-- The stage-1 corrections agree on the bulk edges owned by blocks of `N_1(c₀)`. -/
theorem C0_E {e' : PEdge3 T' w' h'} (hb : ¬ e'.isHalf) (ho : dist3 (owner3 e') c0 ≤ 1) :
    S.C0 (psyn3 E) (ι.E e') = S'.C0 (psyn3 (E ∘ ι.E)) e' := by
  unfold C0
  rw [ι.owner3_E hb, hcov _ ho _ e' rfl hb,
    S'.loc (owner3 e') ((psyn3 E) ∘ ι.V) (psyn3 (E ∘ ι.E)) fun v hv => syn_V hK3 hK4 E ⟨owner3 e', ho, hv⟩]

include hcov hK3 hK4 in
theorem Fcfg_E {e' : PEdge3 T' w' h'} (hb : ¬ e'.isHalf) (ho : dist3 (owner3 e') c0 ≤ 1) :
    S.Fcfg E (ι.E e') = S'.Fcfg (E ∘ ι.E) e' := by
  simp only [Fcfg, Pi.add_apply]
  rw [C0_E hcov hK3 hK4 E hb ho]
  rfl

include hcov hK3 hK4 in
/-- The residuals agree at the checks within distance 34 of `c₀`. -/
theorem psyn3_Fcfg_V {v' : PVert3 T' w' h'} (hv' : distVB v'.toV3 c0 ≤ 34) :
    psyn3 (S.Fcfg E) (ι.V v') = psyn3 (S'.Fcfg (E ∘ ι.E)) v' :=
  sum_ends_V hK3 hK4 (inW3_of_near hv') _ _ fun e' he' =>
    Fcfg_E hcov hK3 hK4 E (hK4 v' (inW3_of_near hv') e' he') (owner3_near he' hv')

include hcov hK1 hK3 hK4 in
theorem flagged_iff : S.flagged E (ι.B c0) ↔ S'.flagged (E ∘ ι.E) c0 := by
  constructor
  · rintro ⟨v, hv, hres⟩
    obtain ⟨v', rfl⟩ := hK1 v ⟨ι.B c0, by rw [dist3_self]; exact Nat.zero_le _,
      inWin_of_distVB (by rw [← hv, distVB_blockOf3]; exact Nat.zero_le _)⟩
    have hv' : blockOf3 v' = c0 := ι.B_inj (by rw [← ι.blockOf3_V]; exact hv)
    have hd : distVB v'.toV3 c0 ≤ 34 := by rw [← hv', distVB_blockOf3]; exact Nat.zero_le _
    exact ⟨v', hv', by rwa [← psyn3_Fcfg_V hcov hK3 hK4 E hd]⟩
  · rintro ⟨v', hv', hres⟩
    have hd : distVB v'.toV3 c0 ≤ 34 := by rw [← hv', distVB_blockOf3]; exact Nat.zero_le _
    exact ⟨ι.V v', by rw [ι.blockOf3_V, hv'], by rwa [psyn3_Fcfg_V hcov hK3 hK4 E hd]⟩

include hcov hK3 hK4 in
/-- A step of `E + C_0` from the image of a check within distance 34 of `c₀` is the image of a step. -/
theorem fadj_V_iff {u' : PVert3 T' w' h'} (hu : distVB u'.toV3 c0 ≤ 34) (v : PVert3 T w h) :
    Fadj (S.Fcfg E) (ι.V u') v ↔ ∃ v', v = ι.V v' ∧ Fadj (S'.Fcfg (E ∘ ι.E)) u' v' := by
  constructor
  · rintro ⟨e, he1, hue, hve⟩
    obtain ⟨e', hb, rfl⟩ := hK3 u' (inW3_of_near hu) e hue
    have hue' : u' ∈ e'.ends := (ι.mem_ends_E hb u').1 hue
    obtain ⟨v', hv'e, rfl⟩ := ι.ends_E_sub hb hve
    exact ⟨v', rfl, e', by rwa [← Fcfg_E hcov hK3 hK4 E hb (owner3_near hue' hu)], hue', hv'e⟩
  · rintro ⟨v', rfl, e', he1, hue', hve'⟩
    have hb := hK4 u' (inW3_of_near hu) e' hue'
    exact ⟨ι.E e', by rwa [Fcfg_E hcov hK3 hK4 E hb (owner3_near hue' hu)], (ι.mem_ends_E hb u').2 hue',
      (ι.mem_ends_E hb v').2 hve'⟩

include hcov hK1 hK3 hK4 in
theorem notLong_iff : NotLong3 (S.Fcfg E) (ι.B c0) ↔ NotLong3 (S'.Fcfg (E ∘ ι.E)) c0 := by
  constructor
  · intro hnl x0' hx0' y' hy'
    -- the image of a walk of the small code is a walk of the large code
    have claim : ∀ z', Relation.ReflTransGen
        (fun u v => Fadj (S'.Fcfg (E ∘ ι.E)) u v ∧ distVB u.toV3 c0 < 35) x0' z' →
        Relation.ReflTransGen (fun u v => Fadj (S.Fcfg E) u v ∧ distVB u.toV3 (ι.B c0) < 35)
          (ι.V x0') (ι.V z') := by
      intro z' hz
      induction hz with
      | refl => exact .refl
      | tail _ hst ih =>
        obtain ⟨hf, hd⟩ := hst
        refine ih.tail ⟨(fadj_V_iff hcov hK3 hK4 E (by omega) _).2 ⟨_, rfl, hf⟩, ?_⟩
        rw [ι.distVB_V]
        exact hd
    have h := hnl (ι.V x0') (by rw [ι.blockOf3_V, hx0']) (ι.V y') (claim y' hy')
    rwa [ι.distVB_V] at h
  · intro hnl x0 hx0 y hy
    obtain ⟨x0', rfl⟩ := hK1 x0 ⟨ι.B c0, by rw [dist3_self]; exact Nat.zero_le _,
      inWin_of_distVB (by rw [← hx0, distVB_blockOf3]; exact Nat.zero_le _)⟩
    have hx0' : blockOf3 x0' = c0 := ι.B_inj (by rw [← ι.blockOf3_V]; exact hx0)
    -- every walk of the large code from an image is the image of a walk of the small code
    have claim : ∀ z, Relation.ReflTransGen (fun u v => Fadj (S.Fcfg E) u v ∧ distVB u.toV3 (ι.B c0) < 35)
        (ι.V x0') z → ∃ z', z = ι.V z' ∧ Relation.ReflTransGen
          (fun u v => Fadj (S'.Fcfg (E ∘ ι.E)) u v ∧ distVB u.toV3 c0 < 35) x0' z' := by
      intro z hz
      induction hz with
      | refl => exact ⟨x0', rfl, .refl⟩
      | tail _ hst ih =>
        obtain ⟨z', rfl, hpz⟩ := ih
        obtain ⟨hf, hd⟩ := hst
        rw [ι.distVB_V] at hd
        obtain ⟨v', rfl, hf'⟩ := (fadj_V_iff hcov hK3 hK4 E (by omega) _).1 hf
        exact ⟨v', rfl, hpz.tail ⟨hf', hd⟩⟩
    obtain ⟨y', rfl, hpy⟩ := claim y hy
    rw [ι.distVB_V]
    exact hnl x0' hx0' y' hpy

include hcov hK1 hK3 hK4 in
/-- **Transport of the bad event** along a covariant embedding. -/
theorem bad_iff_of_emb : S.bad E (ι.B c0) ↔ S'.bad (E ∘ ι.E) c0 :=
  or_congr (flagged_iff hcov hK1 hK3 hK4 E) (not_congr (notLong_iff hcov hK1 hK3 hK4 E))

end transport2

end Stage13

end QECD1
