import QECD1.Cover3

/-!
# Block types and (H_eps) on the 3D code (named hypotheses)

The 3D analogue of the 2D `S3/Hypotheses` (`S3Fam`, `refCol`, `Htype`, `Hstat`). The code of `nt × nx × ny` blocks
(`L = 35`) has `T + 1 = 35 nt` rounds, `w + 1 = 35 nx` columns and `h + 1 = 35 ny` rows. The 25 block types are 5
time types times 5 x types; the y direction is handled by the declared rows.

* `S3Fam3`: the registered stage-1 rules, one `Stage13` for every code size.
* `Htype3 p` (deterministic hypothesis): every undeclared block of every code with `nt, nx, ny ≥ 5`
  has the bad probability of its type's reference block on the reference code of `5 × 5 × 5` blocks. The type of
  block `c` is `(refCol nt c_t, refCol nx c_x)`, and the reference block of type `(i, j)` is `(i, j, 2)`.
* `Hstat3 p ε` (the statistical input): the 25 reference blocks have bad probability at most `ε`.
* `not_bad_of_noCheck`: a block without checks is never bad; `inCode_blockOf3`: every check lies in a block of the
  code.
* `heps_of_types`: `Htype3` and `Hstat3` give (H_eps) on every undeclared block.
* `famEvent_prob_le_types`: the probability of a family's event (`famEvent_prob_le`) with (H_eps) from `Htype3` and
  `Hstat3`.
-/

namespace QECD1

open Classical

/-- The registered stage-1 rules: for block counts `nt, nx, ny`, a rule on the code of `nt × nx × ny` blocks. -/
structure S3Fam3 where
  /-- the stage-1 rule on the code with `T + 1 = 35 nt`, `w + 1 = 35 nx`, `h + 1 = 35 ny` -/
  stage1 : ∀ nt nx ny : ℕ, Stage13 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1)

/-- The type of a block coordinate `a` among `n` blocks: `0`, `1` at the start, `4`, `3` at the end, `2` in the
bulk (2D `refCol`). -/
def refCol (n a : ℕ) : Fin 5 :=
  if a = 0 then 0 else if a = 1 then 1 else if a + 1 = n then 4 else if a + 2 = n then 3 else 2

/-- The reference block of type `(i, j)` on the reference code of `5 × 5 × 5` blocks: time `i`, column `j`, row 2. -/
def refBlock (i j : Fin 5) : V3 := ((i : ℕ), (j : ℕ), 2)

/-- The block lies in the code of `nt × nx × ny` blocks. -/
def InCode (nt nx ny : ℕ) (c : V3) : Prop :=
  0 ≤ c.1 ∧ c.1 < nt ∧ 0 ≤ c.2.1 ∧ c.2.1 < nx ∧ 0 ≤ c.2.2 ∧ c.2.2 < ny

/-- Every check lies in a block of the code. -/
theorem inCode_blockOf3 {nt nx ny : ℕ} (hnt : 1 ≤ nt) (hnx : 1 ≤ nx) (hny : 1 ≤ ny)
    (v : PVert3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1)) : InCode nt nx ny (blockOf3 v) := by
  obtain ⟨t, x, y⟩ := v
  have ht := t.isLt
  have hx := x.isLt
  have hy := y.isLt
  simp only [InCode, blockOf3, blockOf, PVert3.toV3]
  omega

/-- A block without checks is never bad. -/
theorem Stage13.not_bad_of_noCheck {T w h : ℕ} (S : Stage13 T w h) {c : V3}
    (hc : ∀ v : PVert3 T w h, blockOf3 v ≠ c) (E : PEdge3 T w h → ZMod 2) : ¬ S.bad E c := by
  rintro (⟨v, hv, _⟩ | hl)
  · exact hc v hv
  · exact hl fun x0 hx0 => absurd hx0 (hc x0)

namespace S3Fam3

variable (fam : S3Fam3)

/-- **Htype3** (deterministic hypothesis). -/
def Htype3 (p : ℝ) : Prop :=
  ∀ (nt nx ny : ℕ), 5 ≤ nt → 5 ≤ nx → 5 ≤ ny → ∀ c : V3, InCode nt nx ny c → ¬ declared3 ny c →
    prob p (fun X => (fam.stage1 nt nx ny).bad (toZ2 X) c) =
      prob p (fun X => (fam.stage1 5 5 5).bad (toZ2 X) (refBlock (refCol nt c.1.toNat) (refCol nx c.2.1.toNat)))

/-- **Hstat3** (the statistical input): the 25 reference blocks have bad probability at most `ε` at rate `p`. -/
def Hstat3 (p ε : ℝ) : Prop :=
  ∀ i j : Fin 5, prob p (fun X => (fam.stage1 5 5 5).bad (toZ2 X) (refBlock i j)) ≤ ε

/-- **(H_eps) on the undeclared blocks** from the block types and the statistical input. -/
theorem heps_of_types {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (htype : fam.Htype3 p) (hstat : fam.Hstat3 p ε)
    {nt nx ny : ℕ} (hnt : 5 ≤ nt) (hnx : 5 ≤ nx) (hny : 5 ≤ ny) :
    ∀ b : V3, ¬ declared3 ny b → prob p (fun X => (fam.stage1 nt nx ny).bad (toZ2 X) b) ≤ ε := by
  intro b hb
  by_cases hin : InCode nt nx ny b
  · rw [htype nt nx ny hnt hnx hny b hin hb]
    exact hstat _ _
  · have hno : ∀ v : PVert3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1), blockOf3 v ≠ b :=
      fun v hv => hin (hv ▸ inCode_blockOf3 (by omega) (by omega) (by omega) v)
    have h0 : prob p (fun X => (fam.stage1 nt nx ny).bad (toZ2 X) b) = 0 := by
      rw [prob_congr (fun X => show (fam.stage1 nt nx ny).bad (toZ2 X) b ↔ False from
        iff_false_intro (Stage13.not_bad_of_noCheck _ hno _)), prob_false]
    rw [h0]
    exact le_trans (prob_nonneg hp0 hp1 _) (hstat 0 0)

/-- **The probability of a family's event, with (H_eps) from the block types.** On the code of `nt × nx × ny` blocks
(`nt, nx, ny ≥ 5`), under `Htype3` and `Hstat3`, the event that the decoder has a family of `e` containing `x` with
the strip hypotheses, unresolved, has probability at most `∑_{k ∈ K} ε^{|keyBlocks e k.2.2|}` for a finite set `K` of
good skeletons rooted at `e`. -/
theorem famEvent_prob_le_types {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (htype : fam.Htype3 p) (hstat : fam.Hstat3 p ε)
    {nt nx ny : ℕ} (hnt : 5 ≤ nt) (hnx : 5 ≤ nx) (hny : 5 ≤ ny) (reach0 reach1 : Finset V3 → Prop) (e x : V3) :
    ∃ K : Finset Skel3, (∀ k ∈ K, k.1 = e ∧ SkelOK k) ∧
      prob p (fun X => (fam.stage1 nt nx ny).FamEvent reach0 reach1 ny e x (toZ2 X)) ≤
        ∑ k ∈ K, ε ^ (keyBlocks e k.2.2).length :=
  (fam.stage1 nt nx ny).famEvent_prob_le hp0 hp1 (le_trans (prob_nonneg hp0 hp1 _) (hstat 0 0)) ny (by omega)
    {b | ¬ declared3 ny b} (fun _ hb => hb) (fun b hb => fam.heps_of_types hp0 hp1 htype hstat hnt hnx hny b hb)
    reach0 reach1 e x

end S3Fam3

end QECD1
