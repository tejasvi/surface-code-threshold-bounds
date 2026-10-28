import QECML.TwoD.LemmaA
import QECML.Final

/-!
# The 2D lemma split into its two terms

The 2D lemma bounds `Pr(fail)` by a T1 term and a T2 term. The T1 bound counts every *family* with blocks
in both strips (rows `≤ h_s` and `≥ n_y - 1 - h_s`, `h_s = a1/2 + 1`); a spanning family is one of them. The T2
bound covers the failures in which no family has blocks in both strips (the sub-path of Lemma X between the last
bottom-strip family and the first top-strip family after it).

* families: analysis clusters (the `a0`-components of the bad blocks, convention (i) included) linked by the
  decoder's level-1 components (resolved or not);
* `T1 E`: some family has a block in the bottom strip and one in the top strip;
* `H2D_T1`, `H2D_T2`: the two bounds as named hypotheses, with precise events;
* `h2d_of_split` (proved): `H2D_T1 ∧ H2D_T2 ⟹ H2D`, by `P(fail) ≤ P(T1) + P(fail ∧ ¬T1)`.
-/

open Finset Classical

namespace QECML

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- The decoder's level-1 blocks on the syndrome of `E`. -/
def lev1 (a0 : ℕ) (E : G.Ed → ZMod 2) : Set G.Block :=
  S3Geom.level1Set (S3Geom.residD S (psyn G.w G.h E)) a0

/-- Two bad blocks are linked if they lie in one analysis cluster or in one level-1 component. -/
def linked (a0 a1 : ℕ) (E : G.Ed → ZMod 2) (c c' : G.Block) : Prop :=
  S.badD E c ∧ S.badD E c' ∧
    (S.cluster E a0 c = S.cluster E a0 c' ∨
      (c ∈ S.lev1 a0 E ∧ c' ∈ S.lev1 a0 E ∧ G.comp (S.lev1 a0 E) a1 c = G.comp (S.lev1 a0 E) a1 c'))

/-- The family of a bad block. -/
def family (a0 a1 : ℕ) (E : G.Ed → ZMod 2) (c : G.Block) : Set G.Block :=
  {c' | S.badD E c ∧ Relation.ReflTransGen (S.linked a0 a1 E) c c'}

/-- The strip height `h_s = a1/2 + 1`. -/
def hs (a1 : ℕ) : ℕ := a1 / 2 + 1

/-- **T1**: some family has a block in rows `≤ h_s` and a block in rows `≥ n_y - 1 - h_s`. -/
def T1 (a0 a1 : ℕ) (E : G.Ed → ZMod 2) : Prop :=
  ∃ c, S.badD E c ∧ (∃ c1 ∈ S.family a0 a1 E c, c1.2.val ≤ hs a1) ∧
    (∃ c2 ∈ S.family a0 a1 E c, G.ny ≤ c2.2.val + 1 + hs a1)

end Stage1

/-- Failure of a correction decoder on the error `E` (as counted by `pFailCorr`). -/
def failsOn {w h : ℕ} (dec : (PVert w h → ZMod 2) → (PEdge w h → ZMod 2)) (E : PEdge w h → ZMod 2) : Prop :=
  ¬ (psyn w h (dec (psyn w h E)) = psyn w h E ∧ pcls w h (E + dec (psyn w h E)) = 0)

theorem pFailCorr_eq_prob {w h : ℕ} (q : ℝ) (dec : (PVert w h → ZMod 2) → (PEdge w h → ZMod 2)) :
    pFailCorr (bernProd q) (psyn w h) (pcls w h) dec = prob (bernProd q) (failsOn dec) := by
  unfold pFailCorr prob failsOn
  refine Finset.sum_congr rfl fun E _ => ?_
  split_ifs <;> first | rfl | tauto

/-- `P(A) ≤ P(B) + P(A ∧ ¬B)` for a nonnegative weight. -/
theorem prob_le_add {Ω : Type*} [Fintype Ω] {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (A B : Ω → Prop) :
    prob P A ≤ prob P B + prob P (fun ω => A ω ∧ ¬ B ω) := by
  unfold prob
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB, hP ω]

namespace S3Fam

variable (fam : S3Fam)

/-- **H2D_T1** (the T1 term of the 2D lemma; named hypothesis): on every code with `n_x ≥ 5` and
`n_y ≥ nyMin`, Hypothesis (H) at `(q, ε)` implies `P(T1) ≤ C1 n_x e^{-s1 (n_y - H0)}`. -/
def H2D_T1 (a0 a1 : ℕ) (K : BoundConsts) (q ε : ℝ) : Prop :=
  ∀ (nx ny : ℕ) (hnx : 5 ≤ nx) (hny : K.nyMin ≤ ny) (hny1 : 1 ≤ ny),
    (fam.stage1 nx ny (by omega) hny1).HypH q ε →
      prob (bernProd q) (fun E => (fam.stage1 nx ny (by omega) hny1).T1 a0 a1 E) ≤
        K.C1 * nx * Real.exp (-K.s1 * ((ny : ℝ) - K.H0))

/-- **H2D_T2** (the T2 term; named hypothesis): on every code with `n_x ≥ 5` and `n_y ≥ nyMin`, Hypothesis (H)
implies that S3' fails with no family in both strips with probability `≤ C2 n_x e^{-s2 (n_y - H0)}`. -/
def H2D_T2 (a0 a1 : ℕ) (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny))
    (K : BoundConsts) (q ε : ℝ) : Prop :=
  ∀ (nx ny : ℕ) (hnx : 5 ≤ nx) (hny : K.nyMin ≤ ny) (hny1 : 1 ≤ ny),
    (fam.stage1 nx ny (by omega) hny1).HypH q ε →
      prob (bernProd q) (fun E => failsOn (fam.S3decFam a0 a1 Z nx ny) E ∧
          ¬ (fam.stage1 nx ny (by omega) hny1).T1 a0 a1 E) ≤
        K.C2 * nx * Real.exp (-K.s2 * ((ny : ℝ) - K.H0))

/-- **The split is exact for the bound**: `H2D_T1 ∧ H2D_T2 ⟹ H2D` for the Lean decoder S3'. -/
theorem h2d_of_split (a0 a1 : ℕ) (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny))
    (K : BoundConsts) {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h1 : fam.H2D_T1 a0 a1 K q ε)
    (h2 : fam.H2D_T2 a0 a1 Z K q ε) : fam.H2D (fam.S3decFam a0 a1 Z) K q ε := by
  intro nx ny hnx hny hny1 hH
  rw [pFailCorr_eq_prob]
  refine (prob_le_add (bernProd_nonneg hq0 hq1) _
    (fun E => (fam.stage1 nx ny (by omega) hny1).T1 a0 a1 E)).trans ?_
  have e1 := h1 nx ny hnx hny hny1 hH
  have e2 := h2 nx ny hnx hny hny1 hH
  simp only [BoundConsts.eval]
  linarith

end S3Fam

/-- **Theorem B (a1 = 12 constants) with the 2D lemma split into its T1 and T2 terms.** -/
theorem theoremB_a12_split (sp : S3Prog) (hV6 : sp.V6)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hT1 : (sp.toFam hV6).H2D_T1 4 12 constsA12 0.100 5e-4)
    (hT2 : (sp.toFam hV6).H2D_T2 4 12 Z constsA12 0.100 5e-4)
    (htype : (sp.toFam hV6).Htype 0.100) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        9.61e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.0351 * ((nyOf sp.L H : ℝ) - 31)) :=
  theoremB_a12 sp hV6 Z ((sp.toFam hV6).h2d_of_split 4 12 Z constsA12 (by norm_num) (by norm_num) hT1 hT2)
    htype hstat hq hW hH

end QECML
