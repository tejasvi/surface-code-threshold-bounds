import QECD1.TypeFromCov3

/-!
# The named hypotheses of the probability side are satisfiable: the zero stage-1 rule

The zero stage-1 rule (no stage-1 correction) on every code is admissible (`Stage13`: locality and ownership hold
trivially) and translation covariant (`Hcov3`), and `Hstat3` holds for it with `ε = 1` (every probability is at most
`1`). So `famEvent_prob_le_cov` applies to it (`zeroFam3_famEvent`). This is the Lean statement behind the remark that
the zero rule satisfies `Hcov3`.
-/

namespace QECD1

open Classical

/-- The zero stage-1 rule. -/
def zeroStage3 (T w h : ℕ) : Stage13 T w h where
  F _ _ _ := 0
  loc _ _ _ _ := rfl
  own _ _ _ _ := rfl

/-- The zero rule on every code size. -/
def zeroFam3 : S3Fam3 where
  stage1 _ _ _ := zeroStage3 _ _ _

/-- **The zero rule is covariant.** -/
theorem zeroFam3_hcov : zeroFam3.Hcov3 := by
  intro nt nx ny nt' nx' ny' _ _ _ _ _ _ ι c _ D e _ _
  rfl

/-- Every event has probability at most `1`. -/
theorem prob_le_one3 {ι : Type} [Fintype ι] [DecidableEq ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : (ι → Bool) → Prop) : prob p A ≤ 1 := by
  unfold prob
  calc ∑ X, (if A X then pw p X else 0) ≤ ∑ X, pw p X :=
        Finset.sum_le_sum fun X _ => by
          split_ifs
          · exact le_rfl
          · exact pw_nonneg hp0 hp1 X
    _ = 1 := sum_prod_bool p ι

/-- `Hstat3` for the zero rule, with `ε = 1`. -/
theorem zeroFam3_hstat {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : zeroFam3.Hstat3 p 1 :=
  fun _ _ => prob_le_one3 hp0 hp1 _

/-- **`famEvent_prob_le_cov` applies to the zero rule** (codes with at least 5 blocks in each direction). -/
theorem zeroFam3_famEvent {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {nt nx ny : ℕ} (hnt : 5 ≤ nt) (hnx : 5 ≤ nx)
    (hny : 5 ≤ ny) (e x : V3) :
    ∃ K : Finset Skel3, (∀ k ∈ K, k.1 = e ∧ SkelOK k) ∧
      prob p (fun X => (zeroFam3.stage1 nt nx ny).FamEvent (fun _ => False) (fun _ => False) ny e x (toZ2 X)) ≤
        ∑ k ∈ K, (1 : ℝ) ^ (keyBlocks e k.2.2).length :=
  zeroFam3.famEvent_prob_le_cov hp0 hp1 zeroFam3_hcov (zeroFam3_hstat hp0 hp1) hnt hnx hny _ _ e x

end QECD1
