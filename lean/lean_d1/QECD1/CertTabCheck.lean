import QECD1.CertTab
import QECD1.Builder

/-!
# Kernel checks of the builder-form certificate (`λ = 14/1000`, `s = 7/1000`)

`ex_ok`, `famT_ok`, `famY_ok`: the Bellman vectors `exBT`, `famBT`, `famBY` pass `checkN` for the excursion
automaton (52 states) and the family automata of the axes t, x (`stepTT`) and y (`stepTY`) (104 states each),
evaluated by the kernel.
-/

namespace QECD1.Tab

open QECD1.Bld

/-- Table lookups. -/
def stT (j : ℕ) : ℕ := stepTT.getD j 0
def stY (j : ℕ) : ℕ := stepTY.getD j 0
def lf (j : ℕ) : ℕ := leafT.getD j 0
def mkT (n : ℕ) : ℕ := markT.getD n 0
def exB (n : ℕ) : ℕ := exBT.getD n 0
def fBT (n : ℕ) : ℕ := famBT.getD n 0
def fBY (n : ℕ) : ℕ := famBY.getD n 0

theorem ex_ok : checkN 52 (routeMoves lf lf exLinkT) (exE Qden) Qden exB = true := by decide +kernel

theorem famT_ok : checkN 104 (famMoves stT lf linkT mkT) (famE Qden) Qden fBT = true := by decide +kernel

theorem famY_ok : checkN 104 (famMoves stY lf linkT mkT) (famE Qden) Qden fBY = true := by decide +kernel

end QECD1.Tab
