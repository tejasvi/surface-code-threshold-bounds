import QECD1.Walks

/-!
# The exact constants of the 3D deterministic lemma

The constants of the refined 3D T2 count have no slack: one unit the wrong way in `Sw`, `A1`, `A0` or `D` makes the
transfer ratio exceed 1. They are defined here from the level parameters, and each
exact value is a separate theorem, so that the statement of the 3D deterministic lemma and the count use the same
names:

* `D_val : D = 5`, with `D_indep`: `(D - 3) L > 2R` (`70 > 68`), false at `D - 1`;
* `A0_val : A0 = 8` (`A0 = D - 1 + a0`, steps of the selection lemma);
* `A1_val : A1 = 24` (`A1 = D - 1 + a1`, links: exactly one cover offset `D - 1`, see `QECD1.Rooting`);
* `Sw_val : Sw = 17` (`Sw = a1 + 2 - D`, witness span: exactly one cover offset);
* `J_val : J = 17` (`J = a1 + 2 - D`, landing distance: exactly one cover offset);
* `off_val : off = 30` (`off = (1 + κ) D ν`, `κ = 1`, `ν = 3`).

`S0_eq` writes the step offsets `S0` with these names; the landing bound (`landing_le`) sums over `|v|∞ ≥ J` and
the automaton tracks `|z| ≤ Sw - 1`.
-/

namespace QECD1

namespace Const

/-- Block side. -/
def L : ℕ := 35
/-- Window radius (`R = L - 1`). -/
def R : ℕ := 34
/-- Level-0 connection range. -/
def a0 : ℕ := 4
/-- Level-1 connection range. -/
def a1 : ℕ := 20
/-- Independence distance `D = 4 + ⌊2R/L⌋`. -/
def D : ℕ := 4 + 2 * R / L
/-- Step range of the selection lemma. -/
def A0 : ℕ := D - 1 + a0
/-- Link range: one cover offset `D - 1` plus `a1`. -/
def A1 : ℕ := D - 1 + a1
/-- Witness span: `a1 + 1` minus one cover offset `D - 1`. -/
def Sw : ℕ := a1 + 2 - D
/-- Landing distance: `a1 + 1` minus one cover offset `D - 1`. -/
def J : ℕ := a1 + 2 - D
/-- Largest `ℓ1` norm of a corner of the unit cube (three coordinates). -/
def nu : ℕ := 3
/-- Weight ratio of the later stages (unit weights). -/
def kappa : ℕ := 1
/-- Additive constant of the λ-trick. -/
def off : ℕ := (1 + kappa) * D * nu

theorem D_val : D = 5 := by decide

/-- Independence holds at `D` and fails at `D - 1`. -/
theorem D_indep : 2 * R < (D - 3) * L ∧ ¬ (2 * R < (D - 1 - 3) * L) := by decide

theorem A0_val : A0 = 8 := by decide

theorem A1_val : A1 = 24 := by decide

theorem Sw_val : Sw = 17 := by decide

theorem J_val : J = 17 := by decide

theorem off_val : off = 30 := by decide

end Const

/-- The step offsets written with the named constants. -/
theorem S0_eq : S0 = (box Const.A0).filter fun v => Const.D ≤ linf v := by
  rw [Const.A0_val, Const.D_val]
  rfl

end QECD1
