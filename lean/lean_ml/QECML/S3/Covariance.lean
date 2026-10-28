import QECML.S3.Embed

/-!
# Covariance of stage-1 rules along an embedding, and the transport of the bad event

* `Emb.Congr`: a block of `G'` is congruent with its image if every boundary of `G'` it touches is aligned with the
  same boundary of `G` (then the two windows are clipped alike).
* `Stage1.CovOn`: covariance of two stage-1 rules along an embedding on a set of blocks: the output of the image
  block on a syndrome is the push-forward of the output of the block on the pulled-back syndrome.
* `bad_iff_of_emb`: if the windows of `N_1(c₀)` lie in the embedded region, the edges at their checks are images of
  bulk edges, and the rules are covariant on `N_1(c₀)`, then `bad E (ι c₀) ↔ bad (E ∘ ι) c₀`.
-/

open Finset

namespace QECML

namespace S3Geom

namespace Emb

variable {G' G : S3Geom} (ι : Emb G' G)

/-- Congruence of a block of `G'` with its image: each boundary of `G'` touched by the block is aligned with the
same boundary of `G`. -/
def Congr (c : G'.Block) : Prop :=
  (c.1.val = 0 → ι.a = 0) ∧ (c.1.val + 1 = G'.nx → G'.nx + ι.a = G.nx) ∧
    (c.2.val = 0 → ι.b = 0) ∧ (c.2.val + 1 = G'.ny → G'.ny + ι.b = G.ny)

end Emb

end S3Geom

namespace Stage1

variable {G' G : S3Geom}

/-- Covariance of the stage-1 rules `S'` (on `G'`) and `S` (on `G`) along `ι`, for the blocks satisfying `P`. -/
def CovOn (S' : Stage1 G') (S : Stage1 G) (ι : S3Geom.Emb G' G) (P : G'.Block → Prop) : Prop :=
  ∀ c, P c → ∀ (D : G.V → ZMod 2) (e : G'.Ed), G'.owner e = c → S3Geom.isBulk e →
    S.F (ι.B c) D (ι.E e) = S'.F c (D ∘ ι.V) e

section transport

variable (S' : Stage1 G') (S : Stage1 G) (ι : S3Geom.Emb G' G) (c0 : G'.Block)

/-- `v` lies in a window of a block of `N_1(c₀)`. -/
def InW (v : G'.V) : Prop := ∃ c, G'.blockDist c c0 ≤ 1 ∧ G'.distVB v c ≤ G'.R

variable {S' S ι c0}

/-- The edges at the image of a window check are the images of the (bulk) edges at it. -/
theorem filter_ends_V (hK3 : ∀ v', InW c0 v' → ∀ e : G.Ed, ι.V v' ∈ e.ends → ∃ e', S3Geom.isBulk e' ∧ ι.E e' = e)
    (hK4 : ∀ v', InW c0 v' → ∀ e' : G'.Ed, v' ∈ e'.ends → S3Geom.isBulk e') {v' : G'.V} (hv : InW c0 v') :
    univ.filter (fun e : G.Ed => ι.V v' ∈ e.ends) =
      (univ.filter (fun e' : G'.Ed => v' ∈ e'.ends)).image ι.E := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro he
    obtain ⟨e', hb, rfl⟩ := hK3 v' hv e he
    exact ⟨e', (ι.mem_ends_E hb v').1 he, rfl⟩
  · rintro ⟨e', he', rfl⟩
    exact (ι.mem_ends_E (hK4 v' hv e' he') v').2 he'

/-- Sums over the edges at the image of a window check. -/
theorem sum_ends_V (hK3 : ∀ v', InW c0 v' → ∀ e : G.Ed, ι.V v' ∈ e.ends → ∃ e', S3Geom.isBulk e' ∧ ι.E e' = e)
    (hK4 : ∀ v', InW c0 v' → ∀ e' : G'.Ed, v' ∈ e'.ends → S3Geom.isBulk e') {v' : G'.V} (hv : InW c0 v')
    (X : G.Ed → ZMod 2) (X' : G'.Ed → ZMod 2) (hX : ∀ e', v' ∈ e'.ends → X (ι.E e') = X' e') :
    psyn G.w G.h X (ι.V v') = psyn G'.w G'.h X' v' := by
  rw [psyn_apply, psyn_apply]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.sum_filter, filter_ends_V hK3 hK4 hv,
    Finset.sum_image fun x _ y _ h => ι.E_inj h]
  refine Finset.sum_congr rfl fun e' he' => ?_
  exact hX e' (Finset.mem_filter.1 he').2

end transport

section transport2

variable {S' : Stage1 G'} {S : Stage1 G} {ι : S3Geom.Emb G' G} {c0 : G'.Block}
  (hcov : S'.CovOn S ι (fun c => G'.blockDist c c0 ≤ 1))
  (hK1 : ∀ v : G.V, (∃ c : G.Block, G.blockDist c (ι.B c0) ≤ 1 ∧ G.distVB v c ≤ G.R) → ∃ v', ι.V v' = v)
  (hK3 : ∀ v', InW c0 v' → ∀ e : G.Ed, ι.V v' ∈ e.ends → ∃ e', S3Geom.isBulk e' ∧ ι.E e' = e)
  (hK4 : ∀ v', InW c0 v' → ∀ e' : G'.Ed, v' ∈ e'.ends → S3Geom.isBulk e')
  (E : G.Ed → ZMod 2)

include hK3 hK4 in
/-- Syndromes agree at window checks. -/
theorem syn_V {v' : G'.V} (hv : InW c0 v') :
    psyn G.w G.h E (ι.V v') = psyn G'.w G'.h (E ∘ ι.E) v' :=
  sum_ends_V hK3 hK4 hv E (E ∘ ι.E) fun _ _ => rfl

include hcov hK3 hK4 in
/-- The stage-1 corrections agree on the bulk edges owned by blocks of `N_1(c₀)`. -/
theorem C0_E {e' : G'.Ed} (hb : S3Geom.isBulk e') (ho : G'.blockDist (G'.owner e') c0 ≤ 1) :
    S.C0 (psyn G.w G.h E) (ι.E e') = S'.C0 (psyn G'.w G'.h (E ∘ ι.E)) e' := by
  rw [S.C0_apply, S'.C0_apply, ι.owner_E hb, hcov _ ho _ e' rfl hb,
    S'.loc (G'.owner e') ((psyn G.w G.h E) ∘ ι.V) (psyn G'.w G'.h (E ∘ ι.E)) fun v hv =>
      syn_V hK3 hK4 E ⟨G'.owner e', ho, hv⟩]

include hcov hK3 hK4 in
theorem Fcfg_E {e' : G'.Ed} (hb : S3Geom.isBulk e') (ho : G'.blockDist (G'.owner e') c0 ≤ 1) :
    S.Fcfg E (ι.E e') = S'.Fcfg (E ∘ ι.E) e' := by
  simp only [Fcfg, Pi.add_apply]
  rw [C0_E hcov hK3 hK4 E hb ho]
  rfl

theorem inW_of_block {v' : G'.V} (hv : G'.blockDist (G'.blockOf v') c0 ≤ 1) : InW c0 v' :=
  ⟨G'.blockOf v', hv, by rw [G'.distVB_blockOf]; exact Nat.zero_le _⟩

include hcov hK3 hK4 in
/-- The residuals agree at the checks of `c₀`. -/
theorem resid_V {v' : G'.V} (hv' : G'.blockOf v' = c0) : S.resid E (ι.V v') = S'.resid (E ∘ ι.E) v' := by
  have hW : InW c0 v' := inW_of_block (by rw [hv', G'.blockDist_self]; exact Nat.zero_le _)
  simp only [resid, syn, Pi.add_apply]
  rw [syn_V hK3 hK4 E hW]
  congr 1
  exact sum_ends_V hK3 hK4 hW _ _ fun e' he' =>
    C0_E hcov hK3 hK4 E (hK4 v' hW e' he') (by rw [← hv']; exact G'.blockDist_owner e' he')

include hcov hK1 hK3 hK4 in
theorem flagged_iff : S.flagged E (ι.B c0) ↔ S'.flagged (E ∘ ι.E) c0 := by
  constructor
  · rintro ⟨v, hv, hres⟩
    obtain ⟨v', rfl⟩ := hK1 v ⟨ι.B c0, by rw [G.blockDist_self]; exact Nat.zero_le _,
      by rw [← hv, G.distVB_blockOf]; exact Nat.zero_le _⟩
    have hv' : G'.blockOf v' = c0 := ι.B_inj (by rw [← ι.blockOf_V]; exact hv)
    exact ⟨v', hv', by rwa [← resid_V hcov hK3 hK4 E hv']⟩
  · rintro ⟨v', hv', hres⟩
    exact ⟨ι.V v', by rw [ι.blockOf_V, hv'], by rwa [resid_V hcov hK3 hK4 E hv']⟩

include hcov hK3 hK4 in
theorem stepIn_iff {a' b' : G'.V} (ha : G'.blockDist (G'.blockOf a') c0 ≤ 1)
    (hb : G'.blockDist (G'.blockOf b') c0 ≤ 1) :
    S.stepIn E (ι.B c0) (ι.V a') (ι.V b') ↔ S'.stepIn (E ∘ ι.E) c0 a' b' := by
  have hdist : ∀ x' : G'.V, G.blockDist (G.blockOf (ι.V x')) (ι.B c0) = G'.blockDist (G'.blockOf x') c0 :=
    fun x' => by rw [ι.blockOf_V, ι.blockDist_B]
  -- the owner of an edge between two checks of `N_1(c₀)` lies in `N_1(c₀)`
  have hown : ∀ e' : G'.Ed, e'.ends = {a', b'} → G'.blockDist (G'.owner e') c0 ≤ 1 := by
    intro e' he'
    have hlow := G'.lowEnd_mem_ends e'
    rw [he', Finset.mem_insert, Finset.mem_singleton] at hlow
    simp only [S3Geom.owner]
    rcases hlow with h | h <;> rw [h]
    · exact ha
    · exact hb
  simp only [stepIn, hdist]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨e, he, hne, hF⟩
    have hamem : ι.V a' ∈ e.ends := by rw [he]; exact Finset.mem_insert_self _ _
    obtain ⟨e', hb', rfl⟩ := hK3 a' (inW_of_block ha) e hamem
    have hends : e'.ends = {a', b'} := by
      ext x'
      rw [← ι.mem_ends_E hb' x', he, Finset.mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.mem_singleton]
      exact ⟨fun h => h.imp (fun h => ι.V_inj h) (fun h => ι.V_inj h), fun h => h.imp (congrArg ι.V)
        (congrArg ι.V)⟩
    refine ⟨e', hends, fun h => hne (congrArg ι.V h), ?_⟩
    rwa [← Fcfg_E hcov hK3 hK4 E hb' (hown e' hends)]
  · rintro ⟨e', he', hne, hF⟩
    have hb' : S3Geom.isBulk e' := hK4 a' (inW_of_block ha) e' (by rw [he']; exact Finset.mem_insert_self _ _)
    refine ⟨ι.E e', ?_, fun h => hne (ι.V_inj h), by rwa [Fcfg_E hcov hK3 hK4 E hb' (hown e' he')]⟩
    ext u
    rw [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hu
      obtain ⟨x', hx', rfl⟩ := ι.ends_E_sub hb' hu
      rw [he', Finset.mem_insert, Finset.mem_singleton] at hx'
      exact hx'.imp (congrArg ι.V) (congrArg ι.V)
    · rintro (rfl | rfl)
      · exact (ι.mem_ends_E hb' a').2 (by rw [he']; exact Finset.mem_insert_self _ _)
      · exact (ι.mem_ends_E hb' b').2 (by rw [he']; simp)

include hcov hK1 hK3 hK4 in
theorem long_iff : S.long E (ι.B c0) ↔ S'.long (E ∘ ι.E) c0 := by
  have hdist : ∀ x' : G'.V, G.blockDist (G.blockOf (ι.V x')) (ι.B c0) = G'.blockDist (G'.blockOf x') c0 :=
    fun x' => by rw [ι.blockOf_V, ι.blockDist_B]
  constructor
  · rintro ⟨a, b, ha, hLb, hpath⟩
    obtain ⟨a', rfl⟩ := hK1 a ⟨ι.B c0, by rw [G.blockDist_self]; exact Nat.zero_le _,
      by rw [← ha, G.distVB_blockOf]; exact Nat.zero_le _⟩
    have ha' : G'.blockOf a' = c0 := ι.B_inj (by rw [← ι.blockOf_V]; exact ha)
    have claim : ∀ x, Relation.ReflTransGen (S.stepIn E (ι.B c0)) (ι.V a') x →
        ∃ x', x = ι.V x' ∧ G'.blockDist (G'.blockOf x') c0 ≤ 1 ∧
          Relation.ReflTransGen (S'.stepIn (E ∘ ι.E) c0) a' x' := by
      intro x hx
      induction hx with
      | refl => exact ⟨a', rfl, by rw [ha', G'.blockDist_self]; exact Nat.zero_le _, .refl⟩
      | @tail y z _ hyz ih =>
        obtain ⟨y', rfl, hy', hpy⟩ := ih
        have hz : G.blockDist (G.blockOf z) (ι.B c0) ≤ 1 := hyz.2.1
        obtain ⟨z', rfl⟩ := hK1 z ⟨G.blockOf z, hz, by rw [G.distVB_blockOf]; exact Nat.zero_le _⟩
        have hz' : G'.blockDist (G'.blockOf z') c0 ≤ 1 := by rw [← hdist]; exact hz
        exact ⟨z', rfl, hz', hpy.tail ((stepIn_iff hcov hK3 hK4 E hy' hz').1 hyz)⟩
    obtain ⟨b', rfl, _, hpb⟩ := claim b hpath
    refine ⟨a', b', ha', ?_, hpb⟩
    rw [ι.distVB_VB, ← ι.hL] at hLb
    exact hLb
  · rintro ⟨a', b', ha', hLb, hpath⟩
    have claim : ∀ x', Relation.ReflTransGen (S'.stepIn (E ∘ ι.E) c0) a' x' →
        G'.blockDist (G'.blockOf x') c0 ≤ 1 ∧
          Relation.ReflTransGen (S.stepIn E (ι.B c0)) (ι.V a') (ι.V x') := by
      intro x' hx
      induction hx with
      | refl => exact ⟨by rw [ha', G'.blockDist_self]; exact Nat.zero_le _, .refl⟩
      | @tail y' z' _ hyz ih =>
        obtain ⟨hy', hpy⟩ := ih
        have hz' : G'.blockDist (G'.blockOf z') c0 ≤ 1 := hyz.2.1
        exact ⟨hz', hpy.tail ((stepIn_iff hcov hK3 hK4 E hy' hz').2 hyz)⟩
    refine ⟨ι.V a', ι.V b', by rw [ι.blockOf_V, ha'], ?_, (claim b' hpath).2⟩
    rw [ι.distVB_VB, ← ι.hL]
    exact hLb

include hcov hK1 hK3 hK4 in
/-- **Transport of the bad event** along a covariant embedding. -/
theorem bad_iff_of_emb : S.bad E (ι.B c0) ↔ S'.bad (E ∘ ι.E) c0 :=
  or_congr (flagged_iff hcov hK1 hK3 hK4 E) (long_iff hcov hK1 hK3 hK4 E)

end transport2

end Stage1

end QECML
