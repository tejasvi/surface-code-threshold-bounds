import QECML.S3.Decoder

/-!
# The registered stage-1 program and the syndrome-only requirement (V6)

A program may read anything, so it is modelled as a map `P c : E ↦ owned edge set` of the full error. The
syndrome-only requirement (R1), as made explicit in the registration and checked
on the registered code by validation V6, is the named hypothesis `Stage1Prog.SyndromeOnly`: the output of block
`c` depends on the error only through the syndrome in the window of `c`.

Under `SyndromeOnly` the program defines an admissible stage-1 rule (`toStage1`) that agrees with the program on
every error (`toStage1_F_psyn`, `C0_toStage1`). So the bad events of the Lean stage-1 rule are the bad events that
the registered program produces, and the locality lemma `bad_local` applies to them.
-/

open Finset

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-- Every syndrome is the syndrome of some error (the whole code is connected and has rough rows). -/
theorem exists_err (D : G.V → ZMod 2) : ∃ E : G.Ed → ZMod 2, psyn G.w G.h E = D := by
  obtain ⟨X, _, hX⟩ := realizable_of_rough (T := D) conn_univ
    (Set.mem_univ ((⟨0, by omega⟩, ⟨0, by omega⟩) : G.V)) (Or.inl rfl) (fun v _ => Set.mem_univ v)
  exact ⟨X, hX⟩

/-- A fixed error with syndrome `D` (classical choice). -/
noncomputable def errOf (D : G.V → ZMod 2) : G.Ed → ZMod 2 := Classical.choose (exists_err D)

theorem psyn_errOf (D : G.V → ZMod 2) : psyn G.w G.h (errOf D) = D := Classical.choose_spec (exists_err D)

end S3Geom

/-- The registered stage-1 program on a code: for each block, the owned edge set it outputs on the error `E`. -/
structure Stage1Prog (G : S3Geom) where
  P : G.Block → (G.Ed → ZMod 2) → (G.Ed → ZMod 2)
  own : ∀ c E e, G.owner e ≠ c → P c E e = 0

namespace Stage1Prog

variable {G : S3Geom} (P : Stage1Prog G)

/-- **(R1) syndrome-only (validation V6)**: the output of block `c` depends on the error only through the syndrome
in the window of `c`. -/
def SyndromeOnly : Prop :=
  ∀ c E E', (∀ v, G.inWin c v → psyn G.w G.h E v = psyn G.w G.h E' v) → P.P c E = P.P c E'

/-- A syndrome-only program defines an admissible stage-1 rule. -/
noncomputable def toStage1 (hP : P.SyndromeOnly) : Stage1 G where
  F c D := P.P c (S3Geom.errOf D)
  loc c D D' h := hP c _ _ fun v hv => by rw [S3Geom.psyn_errOf, S3Geom.psyn_errOf]; exact h v hv
  own c D e he := P.own c _ e he

/-- The Lean stage-1 rule agrees with the program on every error. -/
theorem toStage1_F_psyn (hP : P.SyndromeOnly) (c : G.Block) (E : G.Ed → ZMod 2) :
    (P.toStage1 hP).F c (psyn G.w G.h E) = P.P c E :=
  hP c _ _ fun v _ => by rw [S3Geom.psyn_errOf]

/-- `C_0` of the Lean stage-1 rule on the syndrome of `E` is the union of the program's outputs on `E`. -/
theorem C0_toStage1 (hP : P.SyndromeOnly) (E : G.Ed → ZMod 2) :
    (P.toStage1 hP).C0 (psyn G.w G.h E) = ∑ c, P.P c E := by
  simp only [Stage1.C0, toStage1_F_psyn]

end Stage1Prog

/-- The registered decoder data with the stage-1 program on every code size. -/
structure S3Prog where
  L : ℕ
  R : ℕ
  hL : 1 ≤ L
  prog : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Stage1Prog ⟨L, R, nx, ny, hL, hnx, hny⟩

namespace S3Prog

variable (sp : S3Prog)

/-- **V6** on every code size. -/
def V6 : Prop := ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), (sp.prog nx ny hnx hny).SyndromeOnly

/-- Under V6, the program family defines the decoder description `S3Fam`. -/
noncomputable def toFam (hV6 : sp.V6) : S3Fam where
  L := sp.L
  R := sp.R
  hL := sp.hL
  stage1 nx ny hnx hny := (sp.prog nx ny hnx hny).toStage1 (hV6 nx ny hnx hny)

end S3Prog

end QECML
