import QECML.S3.Events
import QECML.TheoremB

/-!
# Theorem A from named hypotheses, and Theorem B

The registered decoder S3' is described by `S3Fam`: block side `L`, window radius `R`, and for every code size an
admissible stage-1 rule (`Stage1`: (R1) locality and ownership). The decoder family `dec` (S3' on every code) is a
parameter. Three named hypotheses replace Theorem A:

* `H2D fam dec K q ε` (deterministic; a named hypothesis in this module): the 2D lemma, the failure bound of the
  auxiliary decoder; for the registered parameters it is proved with the Lean constants in `QECML.TwoD.HeadlineFull`. On
  every code with `n_x ≥ 5` and `n_y ≥ nyMin`, Hypothesis (H) at `(q, ε)` for the stage-1 rule of `fam` implies
  `Pr_q(dec fails) ≤ K.eval n_x n_y`.
* `Htype fam q` (equality of block types; a named hypothesis here, derived from `Hcov` in `QECML.S3.TypeFromCov`):
  every block in the sampled rows of every code with
  `n_x, n_y ≥ 5` has the bad probability of its type's reference block on the reference code of `5 × 5` blocks
  (column `0` = L0, `1` = L1, `2` = bulk, `3` = R1, `4` = R0; row `2`).
* `Hstat fam q ε` (statistical; the only statistical input): the five reference blocks have bad probability at most
  `ε` at rate `q`. This is what the pre-registered Monte Carlo certifies (`QECML.CPConfidence`).

Proved here: `theoremA_of_hyps` (independence at block distance `≥ D`, locality, and the per-block hypothesis (H)
are proved in `QECML.S3.Events`), and `theoremB_v2`.
-/

namespace QECML

/-- The registered decoder data, uniform in the code size. -/
structure S3Fam where
  L : ℕ
  R : ℕ
  hL : 1 ≤ L
  /-- the stage-1 rule on the code of `nx × ny` blocks -/
  stage1 : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Stage1 ⟨L, R, nx, ny, hL, hnx, hny⟩

namespace S3Fam

variable (fam : S3Fam)

/-- The geometry of the code of `nx × ny` blocks. -/
abbrev geom (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny) : S3Geom := ⟨fam.L, fam.R, nx, ny, fam.hL, hnx, hny⟩

/-- The reference code of `5 × 5` blocks. -/
abbrev refGeom : S3Geom := fam.geom 5 5 (by norm_num) (by norm_num)

/-- The stage-1 rule on the reference code. -/
abbrev refStage1 : Stage1 fam.refGeom := fam.stage1 5 5 (by norm_num) (by norm_num)

/-- Reference column of a block column `a` of a code with `nx` block columns: `0` (L0), `1` (L1), `4` (R0, last
column), `3` (R1, second to last), `2` (bulk). -/
def refCol (nx a : ℕ) : Fin 5 :=
  if a = 0 then 0 else if a = 1 then 1 else if a + 1 = nx then 4 else if a + 2 = nx then 3 else 2

/-- Reference block of type `t` on the reference code: column `t`, row `2`. -/
def refBlock (t : Fin 5) : fam.refGeom.Block := (t, 2)

/-- **Htype** (equality of block types; deterministic hypothesis). -/
def Htype (q : ℝ) : Prop :=
  ∀ (nx ny : ℕ) (hnx : 5 ≤ nx) (hny : 5 ≤ ny) (c : (fam.geom nx ny (by omega) (by omega)).Block),
    (fam.geom nx ny (by omega) (by omega)).sampledRow c →
    prob (bernProd q) (fun E => (fam.stage1 nx ny (by omega) (by omega)).bad E c) =
      prob (bernProd q) (fun E => fam.refStage1.bad E (fam.refBlock (refCol nx c.1.val)))

/-- **Hstat** (the statistical input): the five reference blocks have bad probability at most `ε` at rate `q`. -/
def Hstat (q ε : ℝ) : Prop :=
  ∀ t : Fin 5, prob (bernProd q) (fun E => fam.refStage1.bad E (fam.refBlock t)) ≤ ε

/-- **H2D** (the 2D lemma; deterministic hypothesis) for the decoder family `dec` built on the stage-1 rules of
`fam`. -/
def H2D (dec : DecoderFamily fam.L) (K : BoundConsts) (q ε : ℝ) : Prop :=
  ∀ (nx ny : ℕ) (hnx : 5 ≤ nx) (hny : K.nyMin ≤ ny) (hny1 : 1 ≤ ny),
    (fam.stage1 nx ny (by omega) hny1).HypH q ε →
      pFailCorr (bernProd q) (psyn (nx * fam.L - 1) (ny * fam.L - 1)) (pcls (nx * fam.L - 1) (ny * fam.L - 1))
        (dec nx ny) ≤ K.eval nx ny

/-- **Theorem A from the named hypotheses.** -/
theorem theoremA_of_hyps (dec : DecoderFamily fam.L) (K : BoundConsts) {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hK : 5 ≤ K.nyMin) (h2d : fam.H2D dec K q ε) (htype : fam.Htype q) (hstat : fam.Hstat q ε) :
    TheoremA K q fam.L dec := by
  intro nx ny hnx hny
  refine h2d nx ny hnx hny (by omega) ?_
  refine Stage1.hypH_of_block_bound _ hq0 hq1 fun c hc => ?_
  rw [htype nx ny hnx (by omega) c hc]
  exact hstat _

/-- **Theorem B from the named hypotheses**, for any bound constants `K` (`n_y ≥ K.nyMin ≥ 5`; `H0` and the
rates are parameters, since `a1` may still be chosen at the certified bound) and any `q* ≤ 1/2`. -/
theorem theoremB_of_hyps (dec : DecoderFamily fam.L) (K : BoundConsts) {qs ε : ℝ} (hqs0 : 0 ≤ qs)
    (hqs : qs ≤ 1 / 2) (hK : 5 ≤ K.nyMin) (h2d : fam.H2D dec K qs ε) (htype : fam.Htype qs)
    (hstat : fam.Hstat qs ε) {q : ℝ} (hq : q ≤ qs) {W H : ℕ} (hW : 1 ≤ W) (hH : K.nyMin * fam.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤ K.eval (nxOf fam.L W) (nyOf fam.L H) :=
  theoremB_of_theoremA K hqs0 hqs fam.hL dec
    (fam.theoremA_of_hyps dec K hqs0 (by linarith) hK h2d htype hstat) hq hW hH

/-- **Theorem B** with the earlier constants `constsV11`: from the 2D lemma (`H2D`), type equality (`Htype`) and the
statistical input (`Hstat`) at `q* = 0.100`, `ε* = 5e-4`: for every `q ≤ 0.100`, `W ≥ 1` and `H ≥ 48 L`,
`P_ML,q(fail) ≤ 7.06e2 n_x e^{-0.1167 (n_y - 47)} + 4.45e6 n_x e^{-0.0257 (n_y - 47)}`,
`n_x = max(5, ⌈W/L⌉)`, `n_y = ⌊H/L⌋`. -/
theorem theoremB_v2 (dec : DecoderFamily fam.L) (h2d : fam.H2D dec constsV11 0.100 5e-4)
    (htype : fam.Htype 0.100) (hstat : fam.Hstat 0.100 5e-4) {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ}
    (hW : 1 ≤ W) (hH : 48 * fam.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      7.06e2 * (nxOf fam.L W : ℝ) * Real.exp (-0.1167 * ((nyOf fam.L H : ℝ) - 47)) +
        4.45e6 * (nxOf fam.L W : ℝ) * Real.exp (-0.0257 * ((nyOf fam.L H : ℝ) - 47)) :=
  theoremB_v1_1 fam.hL dec
    (fam.theoremA_of_hyps dec constsV11 (by norm_num) (by norm_num) (by norm_num [constsV11]) h2d htype hstat)
    hq hW hH

end S3Fam

/-- With `R = L - 1` and `L ≥ 2`, `D = 4 + ⌊2R/L⌋ = 5`. -/
theorem S3Geom.D_eq_five (G : S3Geom) (hR : G.R = G.L - 1) (hL2 : 2 ≤ G.L) : G.D = 5 := by
  have h1 : 2 * G.R / G.L = 1 :=
    Nat.div_eq_of_lt_le (by omega : 1 * G.L ≤ 2 * G.R) (by omega : 2 * G.R < (1 + 1) * G.L)
  simp only [S3Geom.D, h1]

end QECML
