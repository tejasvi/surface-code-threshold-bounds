import QECML.S3.Regions
import QECML.S3.Hypotheses

/-!
# The decoder S3' (the auxiliary decoder) in Lean, and its validity

The auxiliary decoder of the paper, with any admissible stage-1 rule:
* stage 1: `C_0 = ∑_c F_c(D)`, residual `D' = D + ∂C_0`, flagged blocks (those that `D'` meets);
* level 0: the components `K` of the flagged blocks under `ℓ∞` adjacency `≤ a0`, regions `N_r(K)` with
  `r = ⌈a0/2⌉`; `K` is resolved if `D'` has even parity in `K`, or the region reaches row `0` or row `H-1`, or the
  region is the whole code; a resolved `K` gets a correction `C_K` of `D'|K` inside its region;
* level 1: the same rule for the blocks of the unresolved level-0 components, with adjacency `a1`;
* top: `Ω = D'` on the blocks of the unresolved level-1 components, and `C_top` a correction of `Ω` on the whole
  code;
* output `C = C_0 + ∑ C_K + ∑ C_K' + C_top`.

The minimum-weight solver is a parameter (`Solver`): it must return a correction inside the given region whenever
one exists, of minimum weight for its weights `wt`. `S3dec_valid` is the validity proposition: the output is a valid
correction for every syndrome (it uses only the existence part of the solver, as the paper's proof does).
`theoremB_S3` is Theorem B with `H2D` stated for this Lean decoder.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable (G : S3Geom)

/-- `c` and `c'` are blocks of `B` at block distance at most `a`. -/
def adjIn (B : Set G.Block) (a : ℕ) (c c' : G.Block) : Prop := c ∈ B ∧ c' ∈ B ∧ G.blockDist c c' ≤ a

/-- The `a`-component of `c` in `B` (empty if `c ∉ B`). -/
def comp (B : Set G.Block) (a : ℕ) (c : G.Block) : Set G.Block :=
  {c' | c ∈ B ∧ Relation.ReflTransGen (G.adjIn B a) c c'}

/-- Restriction of a syndrome to the checks of the blocks of `K`. -/
noncomputable def restrictTo (K : Set G.Block) (T : G.V → ZMod 2) : G.V → ZMod 2 :=
  fun v => if G.blockOf v ∈ K then T v else 0

/-- The resolution rule of levels 0 and 1. -/
def resolved (Dp : G.V → ZMod 2) (r : ℕ) (K : Set G.Block) : Prop :=
  (∑ v, G.restrictTo K Dp v = 0) ∨ (∃ v ∈ G.region K r, v.2 = 0 ∨ v.2 = Fin.last _) ∨
    (∀ v, v ∈ G.region K r)

/-- The components of `B` under adjacency `a`. -/
noncomputable def comps (B : Set G.Block) (a : ℕ) : Finset (Set G.Block) :=
  (Finset.univ.filter (· ∈ B)).image (G.comp B a)

variable {G}

theorem adjIn_symm {B : Set G.Block} {a : ℕ} {c c' : G.Block} (h : G.adjIn B a c c') : G.adjIn B a c' c :=
  ⟨h.2.1, h.1, by rw [G.blockDist_comm]; exact h.2.2⟩

theorem reachB_symm {B : Set G.Block} {a : ℕ} {c c' : G.Block}
    (h : Relation.ReflTransGen (G.adjIn B a) c c') : Relation.ReflTransGen (G.adjIn B a) c' c := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (adjIn_symm hbc) ih

theorem comp_subset {B : Set G.Block} {a : ℕ} {c : G.Block} : G.comp B a c ⊆ B := by
  intro x ⟨hc, hx⟩
  induction hx with
  | refl => exact hc
  | tail _ hbx _ => exact hbx.2.1

theorem mem_comp_self {B : Set G.Block} {a : ℕ} {c : G.Block} (hc : c ∈ B) : c ∈ G.comp B a c :=
  ⟨hc, .refl⟩

theorem comp_eq_of_mem {B : Set G.Block} {a : ℕ} {c c' : G.Block} (h : c' ∈ G.comp B a c) :
    G.comp B a c' = G.comp B a c := by
  obtain ⟨hc, hcc'⟩ := h
  have hc' : c' ∈ B := comp_subset ⟨hc, hcc'⟩
  ext x
  constructor
  · rintro ⟨_, hx⟩
    exact ⟨hc, hcc'.trans hx⟩
  · rintro ⟨_, hx⟩
    exact ⟨hc', (reachB_symm hcc').trans hx⟩

/-- Blocks of a component are chained inside the component. -/
theorem comp_chain {B : Set G.Block} {a : ℕ} {c : G.Block} (hc : c ∈ B) :
    ∀ c1 ∈ G.comp B a c, ∀ c2 ∈ G.comp B a c, Relation.ReflTransGen
      (fun x y => x ∈ G.comp B a c ∧ y ∈ G.comp B a c ∧ G.blockDist x y ≤ a) c1 c2 := by
  set K := G.comp B a c
  have hfrom : ∀ x, Relation.ReflTransGen (G.adjIn B a) c x →
      Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ G.blockDist x y ≤ a) c x := by
    intro x hx
    induction hx with
    | refl => exact .refl
    | @tail b x hcb hbx ih => exact .tail ih ⟨⟨hc, hcb⟩, ⟨hc, hcb.tail hbx⟩, hbx.2.2⟩
  have hsymm : ∀ {x y}, Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ G.blockDist x y ≤ a) x y →
      Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ G.blockDist x y ≤ a) y x := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact .head ⟨hbc.2.1, hbc.1, by rw [G.blockDist_comm]; exact hbc.2.2⟩ ih
  intro c1 hc1 c2 hc2
  exact (hsymm (hfrom c1 hc1.2)).trans (hfrom c2 hc2.2)

theorem mem_comps_iff {B : Set G.Block} {a : ℕ} {K : Set G.Block} :
    K ∈ G.comps B a ↔ ∃ c ∈ B, G.comp B a c = K := by
  classical
  simp [comps]

/-- Among the components of `B`, the block `b ∈ B` lies exactly in its own. -/
theorem mem_comp_iff_eq {B : Set G.Block} {a : ℕ} {K : Set G.Block} (hK : K ∈ G.comps B a) {b : G.Block}
    (hb : b ∈ B) : b ∈ K ↔ K = G.comp B a b := by
  obtain ⟨c, _, rfl⟩ := mem_comps_iff.1 hK
  constructor
  · intro h
    exact (comp_eq_of_mem h).symm
  · intro h
    rw [h]
    exact mem_comp_self hb

/-- The components of `B` partition `B` (as indicator sums of a restricted syndrome). -/
theorem sum_restrict_comps (B : Set G.Block) (a : ℕ) (P : Set G.Block → Prop) {_hP : DecidablePred P}
    (Dp : G.V → ZMod 2) (v : G.V) :
    ∑ K ∈ (G.comps B a).filter P, G.restrictTo K Dp v =
      if G.blockOf v ∈ B ∧ P (G.comp B a (G.blockOf v)) then Dp v else 0 := by
  simp only [restrictTo]
  split_ifs with h
  · obtain ⟨hb, hP⟩ := h
    rw [Finset.sum_eq_single (G.comp B a (G.blockOf v))]
    · simp [mem_comp_self hb]
    · intro K hK hne
      rw [Finset.mem_filter] at hK
      have : G.blockOf v ∉ K := fun hvK => hne ((mem_comp_iff_eq hK.1 hb).1 hvK)
      simp [this]
    · intro hnot
      exact absurd (Finset.mem_filter.2 ⟨mem_comps_iff.2 ⟨_, hb, rfl⟩, hP⟩) hnot
  · refine Finset.sum_eq_zero fun K hK => ?_
    rw [Finset.mem_filter] at hK
    have : G.blockOf v ∉ K := by
      intro hvK
      obtain ⟨c, _, rfl⟩ := mem_comps_iff.1 hK.1
      have hb : G.blockOf v ∈ B := comp_subset hvK
      exact h ⟨hb, by rw [comp_eq_of_mem hvK]; exact hK.2⟩
    simp [this]

/-- The region of a component is connected. -/
theorem region_comp_conn {B : Set G.Block} {a : ℕ} {c : G.Block} (hc : c ∈ B) :
    G.Conn (G.region (G.comp B a c) ((a + 1) / 2)) :=
  region_conn (by omega) (comp_chain hc)

/-- The whole code is connected. -/
theorem conn_univ : G.Conn (Set.univ : Set G.V) := by
  intro u _ v _
  have hbig : ∀ x : G.V, x ∈ G.box (G.blockOf u) (G.nx + G.ny) := by
    intro x
    show G.blockDist (G.blockOf x) (G.blockOf u) ≤ G.nx + G.ny
    generalize G.blockOf x = b
    generalize G.blockOf u = b'
    have h1 := b.1.isLt
    have h2 := b.2.isLt
    have h3 := b'.1.isLt
    have h4 := b'.2.isLt
    simp only [blockDist, ndist]
    omega
  exact reach_mono (fun _ _ => Set.mem_univ _) (box_conn _ _ u (hbig u) v (hbig v))

end S3Geom

/-- A minimum-weight solver: on a region `U` and a syndrome `T` realizable inside `U`, it returns an edge set inside
`U` with syndrome `T` and minimum weight for its weights `wt` (S3's weights, as discretized by the registered
solver). -/
structure Solver (G : S3Geom) where
  solve : Set G.V → (G.V → ZMod 2) → (G.Ed → ZMod 2)
  wt : G.Ed → ℝ
  correct : ∀ U T, G.Realizable U T → psyn G.w G.h (solve U T) = T
  inside : ∀ U T, G.Realizable U T → G.Inside U (solve U T)
  minimal : ∀ U T X, G.Inside U X → psyn G.w G.h X = T →
    (∑ e, if solve U T e ≠ 0 then wt e else 0) ≤ ∑ e, if X e ≠ 0 then wt e else 0

namespace S3Geom

variable {G : S3Geom}

/-- The residual `D' = D + ∂C_0` as a function of the syndrome. -/
def residD (S : Stage1 G) (D : G.V → ZMod 2) : G.V → ZMod 2 := D + psyn G.w G.h (S.C0 D)

/-- Flagged blocks. -/
def flaggedSet (Dp : G.V → ZMod 2) : Set G.Block := {c | ∃ v, G.blockOf v = c ∧ Dp v ≠ 0}

/-- Blocks passed to level 1: the blocks of the unresolved level-0 components. -/
def level1Set (Dp : G.V → ZMod 2) (a0 : ℕ) : Set G.Block :=
  {c | c ∈ flaggedSet Dp ∧ ¬ G.resolved Dp ((a0 + 1) / 2) (G.comp (flaggedSet Dp) a0 c)}

/-- The top-level syndrome `Ω`: `D'` on the blocks of the unresolved level-1 components. -/
noncomputable def omegaSyn (Dp : G.V → ZMod 2) (a0 a1 : ℕ) : G.V → ZMod 2 := fun v =>
  if G.blockOf v ∈ level1Set Dp a0 ∧
      ¬ G.resolved Dp ((a1 + 1) / 2) (G.comp (level1Set Dp a0) a1 (G.blockOf v)) then Dp v else 0

/-- The corrections of the resolved components of `B` under adjacency `a`. -/
noncomputable def levelSum (Z : Solver G) (Dp : G.V → ZMod 2) (B : Set G.Block) (a : ℕ) : G.Ed → ZMod 2 :=
  ∑ K ∈ (G.comps B a).filter (G.resolved Dp ((a + 1) / 2)),
    Z.solve (G.region K ((a + 1) / 2)) (G.restrictTo K Dp)

/-- **The decoder S3'**: stage-1 rule `S`, adjacencies `a0`, `a1`, minimum-weight solver `Z`. -/
noncomputable def S3dec (S : Stage1 G) (a0 a1 : ℕ) (Z : Solver G) (D : G.V → ZMod 2) : G.Ed → ZMod 2 :=
  S.C0 D + levelSum Z (residD S D) (flaggedSet (residD S D)) a0 +
    levelSum Z (residD S D) (level1Set (residD S D) a0) a1 +
    Z.solve Set.univ (omegaSyn (residD S D) a0 a1)

/-- A resolved component's residual is realizable inside its region. -/
theorem realizable_resolved {B : Set G.Block} {a : ℕ} {c : G.Block} (hc : c ∈ B) {Dp : G.V → ZMod 2}
    (hres : G.resolved Dp ((a + 1) / 2) (G.comp B a c)) :
    G.Realizable (G.region (G.comp B a c) ((a + 1) / 2)) (G.restrictTo (G.comp B a c) Dp) := by
  have hconn := region_comp_conn (a := a) hc
  have hsupp : ∀ v, G.restrictTo (G.comp B a c) Dp v ≠ 0 → v ∈ G.region (G.comp B a c) ((a + 1) / 2) := by
    intro v hv
    simp only [restrictTo] at hv
    split_ifs at hv with h
    · exact ⟨G.blockOf v, h, by rw [G.blockDist_self]; exact Nat.zero_le _⟩
    · exact absurd rfl hv
  rcases hres with heven | ⟨r, hr, hrough⟩ | hall
  · exact realizable_of_even hconn hsupp heven
  · exact realizable_of_rough hconn hr hrough hsupp
  · exact realizable_of_rough hconn (hall (⟨0, by omega⟩, ⟨0, by omega⟩)) (Or.inl rfl) hsupp

theorem psyn_levelSum (Z : Solver G) (Dp : G.V → ZMod 2) (B : Set G.Block) (a : ℕ) :
    psyn G.w G.h (levelSum Z Dp B a) =
      ∑ K ∈ (G.comps B a).filter (G.resolved Dp ((a + 1) / 2)), G.restrictTo K Dp := by
  rw [levelSum, map_sum]
  refine Finset.sum_congr rfl fun K hK => ?_
  obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hK
  obtain ⟨c, hc, rfl⟩ := mem_comps_iff.1 hK1
  exact Z.correct _ _ (realizable_resolved hc hres)

/-- **Validity** of the decoder: for every admissible stage-1 rule and every
minimum-weight solver, the output of S3' is a valid correction for every syndrome. -/
theorem S3dec_valid (S : Stage1 G) (a0 a1 : ℕ) (Z : Solver G) (D : G.V → ZMod 2) :
    psyn G.w G.h (S3dec S a0 a1 Z D) = D := by
  set Dp := residD S D with hDp
  have htop : psyn G.w G.h (Z.solve Set.univ (omegaSyn Dp a0 a1)) = omegaSyn Dp a0 a1 :=
    Z.correct _ _ (realizable_of_rough conn_univ (Set.mem_univ (⟨0, by omega⟩, ⟨0, by omega⟩)) (Or.inl rfl)
      fun v _ => Set.mem_univ v)
  -- the residual is partitioned among the resolved components of both levels and Ω
  have hpart : ∀ v, (∑ K ∈ (G.comps (flaggedSet Dp) a0).filter (G.resolved Dp ((a0 + 1) / 2)),
        G.restrictTo K Dp v) +
      (∑ K ∈ (G.comps (level1Set Dp a0) a1).filter (G.resolved Dp ((a1 + 1) / 2)), G.restrictTo K Dp v) +
      omegaSyn Dp a0 a1 v = Dp v := by
    intro v
    rw [sum_restrict_comps, sum_restrict_comps]
    simp only [omegaSyn]
    by_cases hv : Dp v = 0
    · simp [hv]
    · have hfl : G.blockOf v ∈ flaggedSet Dp := ⟨v, rfl, hv⟩
      by_cases h0 : G.resolved Dp ((a0 + 1) / 2) (G.comp (flaggedSet Dp) a0 (G.blockOf v))
      · have hn1 : G.blockOf v ∉ level1Set Dp a0 := fun h => h.2 h0
        simp [hfl, h0, hn1]
      · have h1 : G.blockOf v ∈ level1Set Dp a0 := ⟨hfl, h0⟩
        by_cases hr1 : G.resolved Dp ((a1 + 1) / 2) (G.comp (level1Set Dp a0) a1 (G.blockOf v))
        · simp [hfl, h0, h1, hr1]
        · simp [hfl, h0, h1, hr1]
  have hC0 : ∀ v, psyn G.w G.h (S.C0 D) v = D v + Dp v := by
    intro v
    simp only [hDp, residD, Pi.add_apply]
    rw [← add_assoc, zmod2_add_self, zero_add]
  show psyn G.w G.h (S.C0 D + levelSum Z Dp (flaggedSet Dp) a0 + levelSum Z Dp (level1Set Dp a0) a1 +
    Z.solve Set.univ (omegaSyn Dp a0 a1)) = D
  rw [map_add, map_add, map_add, psyn_levelSum, psyn_levelSum, htop]
  funext v
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [hC0 v]
  linear_combination hpart v + zmod2_add_self (Dp v)

end S3Geom

namespace S3Fam

variable (fam : S3Fam)

/-- The decoder family S3' built on the stage-1 rules of `fam`, with adjacencies `a0`, `a1` and a solver on every
code size (codes without blocks get the zero decoder, never used). -/
noncomputable def S3decFam (a0 a1 : ℕ)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny)) :
    DecoderFamily fam.L := fun nx ny =>
  if h : 1 ≤ nx ∧ 1 ≤ ny then
    S3Geom.S3dec (fam.stage1 nx ny h.1 h.2) a0 a1 (Z nx ny h.1 h.2)
  else fun _ => 0

/-- **Theorem B with the 2D lemma stated for the Lean decoder S3'.** -/
theorem theoremB_S3 (a0 a1 : ℕ)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny)) (K : BoundConsts)
    {qs ε : ℝ} (hqs0 : 0 ≤ qs) (hqs : qs ≤ 1 / 2) (hK : 5 ≤ K.nyMin)
    (h2d : fam.H2D (fam.S3decFam a0 a1 Z) K qs ε) (htype : fam.Htype qs) (hstat : fam.Hstat qs ε)
    {q : ℝ} (hq : q ≤ qs) {W H : ℕ} (hW : 1 ≤ W) (hH : K.nyMin * fam.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤ K.eval (nxOf fam.L W) (nyOf fam.L H) :=
  fam.theoremB_of_hyps _ K hqs0 hqs hK h2d htype hstat hq hW hH

/-- Validity of every decoder of the family on every code with at least one block. -/
theorem S3decFam_valid (a0 a1 : ℕ)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny)) (nx ny : ℕ)
    (hnx : 1 ≤ nx) (hny : 1 ≤ ny) (D : PVert (nx * fam.L - 1) (ny * fam.L - 1) → ZMod 2) :
    psyn _ _ (fam.S3decFam a0 a1 Z nx ny D) = D := by
  unfold S3decFam
  split_ifs with h
  · exact S3Geom.S3dec_valid (G := fam.geom nx ny h.1 h.2) (fam.stage1 nx ny h.1 h.2) a0 a1
      (Z nx ny h.1 h.2) D
  · exact absurd ⟨hnx, hny⟩ h

end S3Fam

end QECML
