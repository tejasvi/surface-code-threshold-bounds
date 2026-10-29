import QECD1.Params

/-!
# Move lists of the refined 3D T2 count, built from weight tables

States of the route automaton of one axis are numbered `0 = B`, `1..33 = A(z)` with `z = n - 17` (`|z| ≤ 16`),
`34 = Asp`, `35..51 = C(z)` with `z = n - 43` (`|z| ≤ 8`); offsets `|k| ≤ 8` are numbered `j = k + 8 < 17`. The
family automaton has the states `n < 52` before the mark and `n + 52` after it. The weights are natural-number
numerators over a common denominator `Q`. The numbering is that of `Sw = 17` and `A0 = 8` (`17 = Sw` A-states on
each side of 0, `17 = 2 A0 + 1` offsets). The Asp threshold of `aNext` is written with `Const.Sw` and `Const.A0`, so
a change of the level parameters cannot leave a stale literal there.

* `aNext n j`: the state after a step `k = j - A0` from the A-state `n` (`z = n - Sw`); it is `Asp` (`2 Sw`) once
  `|z + k| ≥ Sw`, i.e. `n + j ≤ A0` or `2 Sw + A0 ≤ n + j`.
* `routeMoves step leaf link n`: `B --step k--> A(k)`, `B --leaf k--> C(k)`; `A(z) --step k--> aNext`,
  `A(z) --link--> B`; `Asp --steps--> Asp` (one lumped move), `Asp --link--> B`; `C(z) --link--> B`. No link leaves
  `B` (the leaf convention of the 2D proof).
* `famMoves`: the route moves, plus the mark `n --mark--> n + 52` before the mark; after it the route moves shifted
  by `52`. End weights `famE`: `0` before the mark and at `(B, after)`, `Q` elsewhere.
* `exE`: the excursion automaton ends only in `Asp`.
* `checkN`: the Bellman check, one natural-number inequality per state; `checkN_spec` reads it off.
-/

namespace QECD1.Bld

/-- The A-state index after a step with table index `j` (offset `j - A0`) from the A-state index `n`. -/
def aNext (n j : ℕ) : ℕ :=
  if n + j ≤ Const.A0 ∨ 2 * Const.Sw + Const.A0 ≤ n + j then 2 * Const.Sw else n + j - Const.A0

/-- At the registered values `aNext` is the literal rule `Asp` (34) for `n + j ≤ 8` or `42 ≤ n + j`. -/
theorem aNext_eq (n j : ℕ) : aNext n j = if n + j ≤ 8 ∨ 42 ≤ n + j then 34 else n + j - 8 := by
  unfold aNext
  rw [Const.Sw_val, Const.A0_val]

/-- The route moves of state `n < 52`. -/
def routeMoves (step leaf : ℕ → ℕ) (link n : ℕ) : List (ℕ × ℕ) :=
  if n = 0 then (List.range 17).map (fun j => (step j, j + 9)) ++ (List.range 17).map (fun j => (leaf j, j + 35))
  else if n ≤ 33 then (List.range 17).map (fun j => (step j, aNext n j)) ++ [(link, 0)]
  else if n = 34 then [(((List.range 17).map step).sum, 34), (link, 0)]
  else [(link, 0)]

/-- The family moves of state `n < 104`. -/
def famMoves (step leaf : ℕ → ℕ) (link : ℕ) (mark : ℕ → ℕ) (n : ℕ) : List (ℕ × ℕ) :=
  if n < 52 then routeMoves step leaf link n ++ [(mark n, n + 52)]
  else (routeMoves step leaf link (n - 52)).map fun m => (m.1, m.2 + 52)

/-- Family end weights: `0` before the mark and at `(B, after)`. -/
def famE (Q n : ℕ) : ℕ := if n ≤ 52 then 0 else Q

/-- Excursion end weights: only `Asp`. -/
def exE (Q n : ℕ) : ℕ := if n = 34 then Q else 0

/-- The Bellman check: one natural-number inequality per state `q < n`. -/
def checkN (n : ℕ) (moves : ℕ → List (ℕ × ℕ)) (e : ℕ → ℕ) (Q : ℕ) (B : ℕ → ℕ) : Bool :=
  (List.range n).all fun q => decide (e q * Q + ((moves q).map fun m => m.1 * B m.2).sum ≤ B q * Q)

theorem checkN_spec {n : ℕ} {moves : ℕ → List (ℕ × ℕ)} {e : ℕ → ℕ} {Q : ℕ} {B : ℕ → ℕ}
    (h : checkN n moves e Q B = true) (q : ℕ) (hq : q < n) :
    e q * Q + ((moves q).map fun m => m.1 * B m.2).sum ≤ B q * Q := by
  unfold checkN at h
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h q (List.mem_range.2 hq))

end QECD1.Bld
