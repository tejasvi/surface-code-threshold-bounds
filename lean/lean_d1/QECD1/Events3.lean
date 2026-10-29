import QECD1.ProbRows3

/-!
# The stage-1 rule, the bad event of a block, and its locality on the 3D code

This is the 3D analogue of the 2D `S3/Geometry` (`lowEnd`, `owner`) and `S3/Events` (`Stage1`, `C0`, `bad`,
`bad_local`).

* `lowEnd3`, `owner3`: an edge is owned by the block of its lower end (the check of a half-edge). If an end of `e` is
  within `ℓ∞` distance 34 of block `c`, the owner of `e` is in `N_1(c)` (`owner3_near`).
* `Stage13` ((R1) locality and ownership): for each block `c` a map `F c` from syndromes to edge sets that
  reads the syndrome only in the window of `c` (`InWin`) and returns only edges owned by `c`.
* `C0` (on each edge, the output of its owner; by ownership this is the sum of all outputs), `Fcfg` (`E + C_0`, the
  configuration `X` of `gen_skel3_final`), `flagged` (the residual `psyn3 (E + C_0)`, which is `D + ∂C_0` by
  `psyn3_Fcfg`, meets the block), `long` (the negation of `NotLong3`), `bad` (flagged or long). Declared blocks are bad
  by convention (i); that is not a noise event and enters through the sampled rows.
* `bad_local`: `bad E c` depends only on `E` on `Nbhd3 c`. `bad_dependsOn` states it for Boolean
  configurations (`toZ2`), and `bad_prob_le_rows` discharges the locality hypothesis of `skel_prob_le_rows`.
-/

namespace QECD1

open Classical

variable {T w h : ℕ}

/-- The lower end of an edge: the end with the smaller coordinate, or the check of a half-edge. -/
def lowEnd3 : PEdge3 T w h → PVert3 T w h
  | .hor t x y => (t, x.castSucc, y)
  | .ver t x y => (t, x, y.castSucc)
  | .time t x y => (t.castSucc, x, y)
  | .bot t x => (t, x, 0)
  | .top t x => (t, x, Fin.last h)

theorem lowEnd3_mem_ends (e : PEdge3 T w h) : lowEnd3 e ∈ e.ends := by
  cases e <;> simp [lowEnd3, PEdge3.ends]

/-- The block that owns an edge: the block of its lower end. -/
def owner3 (e : PEdge3 T w h) : V3 := blockOf3 (lowEnd3 e)

theorem distVB_blockOf3 (v : PVert3 T w h) : distVB v.toV3 (blockOf3 v) = 0 :=
  distVB_blockOf v.toV3

/-- A check within `ℓ∞` distance 34 of block `c` lies in the window of `c`. -/
theorem inWin_of_distVB {p c : V3} (hd : distVB p c ≤ 34) : InWin c p := by
  simp only [distVB, max_le_iff, dist1] at hd
  obtain ⟨h1, h2, h3⟩ := hd
  intro i
  fin_cases i
  · show c.1 * 35 - 34 ≤ p.1 ∧ p.1 ≤ c.1 * 35 + 34 + 34
    omega
  · show c.2.1 * 35 - 34 ≤ p.2.1 ∧ p.2.1 ≤ c.2.1 * 35 + 34 + 34
    omega
  · show c.2.2 * 35 - 34 ≤ p.2.2 ∧ p.2.2 ≤ c.2.2 * 35 + 34 + 34
    omega

/-- If an end of `e` is within distance 34 of block `c`, the owner of `e` is in `N_1(c)`. -/
theorem owner3_near {e : PEdge3 T w h} {u : PVert3 T w h} {c : V3} (hu : u ∈ e.ends) (hd : distVB u.toV3 c ≤ 34) :
    dist3 (owner3 e) c ≤ 1 := by
  have h1 := distVB_lip u.toV3 (lowEnd3 e).toV3 c (ends_adjacent e hu (lowEnd3_mem_ends e))
  exact blockOf_near _ c (by omega)

theorem mem_nbhd3 {e : PEdge3 T w h} {c b : V3} {v : PVert3 T w h} (hv : v ∈ e.ends) (hb : dist3 b c ≤ 1)
    (hw : InWin b v.toV3) : e ∈ Nbhd3 c :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, v, hv, b, hb, hw⟩

theorem psyn3_congr {E E' : PEdge3 T w h → ZMod 2} {v : PVert3 T w h}
    (hE : ∀ e : PEdge3 T w h, v ∈ e.ends → E e = E' e) :
    psyn3 E v = psyn3 E' v := by
  unfold psyn3
  exact Finset.sum_congr rfl fun e he => hE e (Finset.mem_filter.1 he).2

/-- A Boolean configuration as an edge set. -/
def toZ2 (X : PEdge3 T w h → Bool) : PEdge3 T w h → ZMod 2 := fun e => if X e then 1 else 0

/-- An admissible stage-1 rule on the 3D code ((R1) locality and ownership; 2D `Stage1`). -/
structure Stage13 (T w h : ℕ) where
  /-- the owned output of block `c` on the syndrome `D` -/
  F : V3 → (PVert3 T w h → ZMod 2) → (PEdge3 T w h → ZMod 2)
  /-- (R1) locality: `F c` reads the syndrome only in the window of `c` -/
  loc : ∀ c D D', (∀ v : PVert3 T w h, InWin c v.toV3 → D v = D' v) → F c D = F c D'
  /-- ownership: `F c` returns only edges owned by `c` -/
  own : ∀ c D e, owner3 e ≠ c → F c D e = 0

namespace Stage13

variable (S : Stage13 T w h)

/-- `C_0` on an edge: the output of its owner. By ownership this is the sum of the outputs of all blocks. -/
def C0 (D : PVert3 T w h → ZMod 2) (e : PEdge3 T w h) : ZMod 2 := S.F (owner3 e) D e

/-- `F = E + C_0`, the configuration `X` to which `gen_skel3_final` is applied. -/
def Fcfg (E : PEdge3 T w h → ZMod 2) : PEdge3 T w h → ZMod 2 := E + S.C0 (psyn3 E)

/-- The residual of `E + C_0` is `D + ∂C_0` with `D = psyn3 E` (2D `resid`). -/
theorem psyn3_Fcfg (E : PEdge3 T w h → ZMod 2) : psyn3 (S.Fcfg E) = psyn3 E + psyn3 (S.C0 (psyn3 E)) :=
  psyn3_add _ _

/-- Block `c` is flagged if the residual meets it. -/
def flagged (E : PEdge3 T w h → ZMod 2) (c : V3) : Prop :=
  ∃ v : PVert3 T w h, blockOf3 v = c ∧ psyn3 (S.Fcfg E) v ≠ 0

/-- Block `c` is long if an `F`-walk inside `{distVB · c < 35}` from a check of `c` reaches distance 35. -/
def long (E : PEdge3 T w h → ZMod 2) (c : V3) : Prop := ¬ NotLong3 (S.Fcfg E) c

/-- The bad event of block `c`: flagged or long. -/
def bad (E : PEdge3 T w h → ZMod 2) (c : V3) : Prop := S.flagged E c ∨ S.long E c

/-! ## Locality -/

variable {S}

/-- Agreement on `Nbhd3 c` gives agreement of `E + C_0` on every edge with an end within distance 34 of `c`. -/
theorem Fcfg_congr {E E' : PEdge3 T w h → ZMod 2} {c : V3} (hEE : ∀ e ∈ Nbhd3 c, E e = E' e)
    {e : PEdge3 T w h} {u : PVert3 T w h} (hu : u ∈ e.ends) (hd : distVB u.toV3 c ≤ 34) :
    S.Fcfg E e = S.Fcfg E' e := by
  have hown := owner3_near hu hd
  have hC : S.C0 (psyn3 E) e = S.C0 (psyn3 E') e :=
    congrFun (S.loc (owner3 e) (psyn3 E) (psyn3 E') fun v hv =>
      psyn3_congr fun e' he' => hEE e' (mem_nbhd3 he' hown hv)) e
  have hE : E e = E' e := hEE e (mem_nbhd3 hu (by rw [dist3_self]; exact Nat.zero_le _) (inWin_of_distVB hd))
  simp only [Fcfg, Pi.add_apply]
  rw [hC, hE]

theorem psyn3_Fcfg_congr {E E' : PEdge3 T w h → ZMod 2} {c : V3} (hEE : ∀ e ∈ Nbhd3 c, E e = E' e)
    {v : PVert3 T w h} (hv : blockOf3 v = c) : psyn3 (S.Fcfg E) v = psyn3 (S.Fcfg E') v :=
  psyn3_congr fun _ he => Fcfg_congr hEE he (by rw [← hv, distVB_blockOf3]; exact Nat.zero_le _)

theorem notLong_congr {E E' : PEdge3 T w h → ZMod 2} {c : V3} (hEE : ∀ e ∈ Nbhd3 c, E e = E' e) :
    NotLong3 (S.Fcfg E) c ↔ NotLong3 (S.Fcfg E') c := by
  have hstep : (fun u v : PVert3 T w h => Fadj (S.Fcfg E) u v ∧ distVB u.toV3 c < 35) =
      (fun u v => Fadj (S.Fcfg E') u v ∧ distVB u.toV3 c < 35) := by
    funext u v
    refine propext (and_congr_left fun hu => exists_congr fun e => ?_)
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(Fcfg_congr hEE h2 (by omega)).symm.trans h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(Fcfg_congr hEE h2 (by omega)).trans h1, h2, h3⟩
  unfold NotLong3
  rw [hstep]

/-- **Locality on the 3D code**: the bad event of `c` depends only on the errors on `Nbhd3 c`. -/
theorem bad_local {E E' : PEdge3 T w h → ZMod 2} {c : V3} (hEE : ∀ e ∈ Nbhd3 c, E e = E' e) :
    S.bad E c ↔ S.bad E' c := by
  unfold bad flagged long
  rw [notLong_congr hEE]
  refine or_congr (exists_congr fun v => and_congr_right fun hv => ?_) Iff.rfl
  rw [psyn3_Fcfg_congr hEE hv]

variable (S)

/-- Locality for Boolean configurations: the event "`c` is bad" depends only on `Nbhd3 c`. -/
theorem bad_dependsOn (c : V3) : DependsOn (fun X : PEdge3 T w h → Bool => S.bad (toZ2 X) c) (Nbhd3 c) :=
  fun X Y hXY => bad_local fun e he => by simp only [toZ2, hXY e he]

/-- **The product bound for the decoder's bad events**, with locality proved: pairwise `D`-separated blocks in the
sampled rows `R` are all bad with probability at most `ε^{|B|}`, if (H_eps) holds on `R`. -/
theorem bad_prob_le_rows {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε) (R : Set V3)
    (hε : ∀ b ∈ R, prob p (fun X => S.bad (toZ2 X) b) ≤ ε) {B : List V3}
    (hB : B.Pairwise (fun a b => Const.D ≤ dist3 a b)) (hBR : ∀ b ∈ B, b ∈ R) :
    prob p (fun X => ∀ b ∈ B, S.bad (toZ2 X) b) ≤ ε ^ B.length :=
  skel_prob_le_rows hp0 hp1 hε0 (fun b X => S.bad (toZ2 X) b) S.bad_dependsOn R hε hB hBR

end Stage13

end QECD1
