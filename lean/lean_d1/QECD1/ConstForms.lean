import QECD1.Witness
import QECD1.RatioS

/-!
# The witness and landing thresholds written with the named constants

`Walks`, `Landing` and `RatioS` are imported by `Params` or hold numerics for the registered values, so they state the
witness span and the landing distance with the literal `17`. This module restates them with `Const.Sw` and `Const.J`.
A later change of `L`, `R`, `a0` or `a1` then fails here, at `Const.Sw_val` / `Const.J_val`, instead of leaving a
stale literal.

* `Ncnt_zero_const`: the 0-step witness count is `[Sw ≤ |z|]`.
* `span_indicator_le_const`: the union over the axes with threshold `Sw`.
* `landing_tilt_le_const`: the tilted landing bound for landing sets with `|v|∞ ≥ J`.

The definitions `witWt`, `witOn` (Witness), `jok3` (Transfer) and `aNext` (Builder) are written with `Const.Sw`,
`Const.J` and `Const.A0` directly.
-/

namespace QECD1

theorem Ncnt_zero_const (z : ℤ) : Ncnt 0 z = if Const.Sw ≤ z.natAbs then 1 else 0 := by
  rw [Const.Sw_val]
  rfl

theorem span_indicator_le_const (z : V3) :
    (if Const.Sw ≤ linf z then (1 : ℝ) else 0) ≤
      (if Const.Sw ≤ z.1.natAbs then 1 else 0) + (if Const.Sw ≤ z.2.1.natAbs then 1 else 0) +
        (if Const.Sw ≤ z.2.2.natAbs then 1 else 0) := by
  rw [Const.Sw_val]
  exact span_indicator_le z

theorem landing_tilt_le_const (S : Finset V3) (hS : ∀ v ∈ S, Const.J ≤ linf v) :
    ∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2) ≤ Jbar2 :=
  landing_tilt_le S fun v hv => by
    have h := hS v hv
    rw [Const.J_val] at h
    exact h

end QECD1
