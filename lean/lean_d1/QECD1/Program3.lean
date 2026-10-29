import QECD1.T2Final3
import QECD1.NonVacCov3

/-!
# The registered stage-1 program and the syndrome-only requirement (V6), 3D

The 3D analogue of the 2D `S3/Program`. A program may read anything, so it is modelled as a map
`P c : E ↦ owned edge set` of the full error (`Stage1Prog3`). The syndrome-only requirement (R1),
checked on the registered code by validation V6, is the named hypothesis `Stage1Prog3.SyndromeOnly`: the output of
block `c` depends on the error only through the syndrome in the window of `c`.

Under `SyndromeOnly` the program defines an admissible stage-1 rule (`toStage13`) that agrees with the program on
every error (`toStage13_F_psyn`, `C0_toStage13`, `Fcfg_toStage13`). So the bad events of the Lean stage-1 rule are the
bad events that the registered program produces, and locality (`bad_local`) and the bounds of this development apply
to them. `S3Prog3.toFam3` gives the decoder family on every code size under V6; `Hcov3` for it remains the named
covariance hypothesis (validation V2).
-/

namespace QECD1

variable {T w h : ℕ}

/-- A fixed error with syndrome `D` (classical choice; every syndrome is realizable, `psyn3_surj`). -/
noncomputable def errOf3 (D : PVert3 T w h → ZMod 2) : PEdge3 T w h → ZMod 2 := Classical.choose (psyn3_surj D)

theorem psyn3_errOf3 (D : PVert3 T w h → ZMod 2) : psyn3 (errOf3 D) = D := Classical.choose_spec (psyn3_surj D)

/-- The registered stage-1 program on a code: for each block, the owned edge set it outputs on the error `E`. -/
structure Stage1Prog3 (T w h : ℕ) where
  P : V3 → (PEdge3 T w h → ZMod 2) → (PEdge3 T w h → ZMod 2)
  own : ∀ c E e, owner3 e ≠ c → P c E e = 0

namespace Stage1Prog3

variable (P : Stage1Prog3 T w h)

/-- **(R1) syndrome-only (validation V6)**: the output of block `c` depends on the error only through the syndrome
in the window of `c`. -/
def SyndromeOnly : Prop :=
  ∀ c E E', (∀ v : PVert3 T w h, InWin c v.toV3 → psyn3 E v = psyn3 E' v) → P.P c E = P.P c E'

/-- A syndrome-only program defines an admissible stage-1 rule. -/
noncomputable def toStage13 (hP : P.SyndromeOnly) : Stage13 T w h where
  F c D := P.P c (errOf3 D)
  loc c D D' hDD := hP c _ _ fun v hv => by rw [psyn3_errOf3, psyn3_errOf3]; exact hDD v hv
  own c D e he := P.own c _ e he

/-- The Lean stage-1 rule agrees with the program on every error. -/
theorem toStage13_F_psyn (hP : P.SyndromeOnly) (c : V3) (E : PEdge3 T w h → ZMod 2) :
    (P.toStage13 hP).F c (psyn3 E) = P.P c E :=
  hP c _ _ fun v _ => by rw [psyn3_errOf3]

/-- `C_0` of the Lean stage-1 rule on the syndrome of `E`: each edge gets its owner block's output. -/
theorem C0_toStage13 (hP : P.SyndromeOnly) (E : PEdge3 T w h → ZMod 2) :
    (P.toStage13 hP).C0 (psyn3 E) = fun e => P.P (owner3 e) E e := by
  funext e
  show (P.toStage13 hP).F (owner3 e) (psyn3 E) e = P.P (owner3 e) E e
  rw [toStage13_F_psyn]

/-- The stage-1 residual of the Lean rule is the program's: `E` plus the owners' outputs. -/
theorem Fcfg_toStage13 (hP : P.SyndromeOnly) (E : PEdge3 T w h → ZMod 2) :
    (P.toStage13 hP).Fcfg E = E + fun e => P.P (owner3 e) E e := by
  show E + (P.toStage13 hP).C0 (psyn3 E) = _
  rw [C0_toStage13]

end Stage1Prog3

/-- The registered stage-1 program on every code size (`n_t × n_x × n_y` blocks of side `L = 35`). -/
structure S3Prog3 where
  prog : ∀ nt nx ny : ℕ, Stage1Prog3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1)

namespace S3Prog3

variable (sp : S3Prog3)

/-- **V6** on every code size. -/
def V6 : Prop := ∀ nt nx ny : ℕ, (sp.prog nt nx ny).SyndromeOnly

/-- Under V6, the program family defines the decoder description `S3Fam3`. -/
noncomputable def toFam3 (hV6 : sp.V6) : S3Fam3 where
  stage1 nt nx ny := (sp.prog nt nx ny).toStage13 (hV6 nt nx ny)

/-- The stage-1 residual of the decoder family is the program's on every code size. -/
theorem toFam3_Fcfg (hV6 : sp.V6) (nt nx ny : ℕ) (E : PEdge3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1) → ZMod 2) :
    ((sp.toFam3 hV6).stage1 nt nx ny).Fcfg E = E + fun e => (sp.prog nt nx ny).P (owner3 e) E e :=
  (sp.prog nt nx ny).Fcfg_toStage13 (hV6 nt nx ny) E

end S3Prog3

end QECD1
