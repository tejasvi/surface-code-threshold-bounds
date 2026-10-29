import QECD1.Selection3
import QECD1.Weights

/-!
# Independence at `D = 5` in 3D (block side `L = 35`, window radius `R = 34`)

The bad event of a block `c` depends only on the edges with an endpoint in the window of a block of `N_1(c)`, the
blocks within `ℓ∞` distance 1 of `c`. Block `b` covers the checks `p` with
`b_i L ≤ p_i ≤ b_i L + L - 1` in each coordinate `i` (t, x, y). Its window of radius `R` is
`b_i L - R ≤ p_i ≤ b_i L + L - 1 + R` (`InWin`); time windows have the same radius.

* `indep_windows`: suppose `|c - c'|∞ ≥ D = 5`. Then every check in the window of a block of `N_1(c)` and every check
  in the window of a block of `N_1(c')` are at `ℓ∞` distance at least 2. In the separating coordinate,
  `(D - 3) L + 1 - 2R = 3 ≥ 2`, which is `(D - 3) L > 2R` (`Const.D_indep`).
* `no_common_edge`: so no edge (`ℓ∞` length at most 1, or a single check) has an endpoint in both windows: the two
  bad events depend on disjoint edge sets, hence are independent under the product noise.
* `indep_fails_D4`: at distance 4 the windows of `N_1(c)` and `N_1(c')` share a check, so `D = 4` does not give
  independence. Hence `D = 5` is exact.
-/

namespace QECD1

/-- Check `p` lies in the window of radius `R = 34` around the checks of block `b` (`L = 35`). -/
def InWin (b p : V3) : Prop :=
  ∀ i : Fin 3, coord i b * 35 - 34 ≤ coord i p ∧ coord i p ≤ coord i b * 35 + 34 + 34

instance (b p : V3) : Decidable (InWin b p) := by
  unfold InWin
  infer_instance

theorem InWin_const (b p : V3) :
    InWin b p ↔ ∀ i : Fin 3, coord i b * (Const.L : ℤ) - Const.R ≤ coord i p ∧
      coord i p ≤ coord i b * (Const.L : ℤ) + ((Const.L : ℤ) - 1) + Const.R := by
  unfold InWin
  simp only [Const.L, Const.R]
  norm_num

/-- One coordinate of the separation argument. -/
theorem sep_coord (ci ci' bi bi' pi pi' : ℤ) (hc : 5 ≤ (ci - ci').natAbs) (hb : (bi - ci).natAbs ≤ 1)
    (hb' : (bi' - ci').natAbs ≤ 1) (hp1 : bi * 35 - 34 ≤ pi) (hp2 : pi ≤ bi * 35 + 34 + 34)
    (hq1 : bi' * 35 - 34 ≤ pi') (hq2 : pi' ≤ bi' * 35 + 34 + 34) : 2 ≤ (pi - pi').natAbs := by
  omega

/-- **Independence at `D = 5`.** -/
theorem indep_windows (c c' b b' p p' : V3) (hcc : Const.D ≤ dist3 c c') (hb : dist3 b c ≤ 1)
    (hb' : dist3 b' c' ≤ 1) (hp : InWin b p) (hp' : InWin b' p') : 2 ≤ linf (p - p') := by
  rw [Const.D_val] at hcc
  simp only [dist3, linf, Prod.fst_sub, Prod.snd_sub, max_le_iff, le_max_iff] at hcc hb hb' ⊢
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h0' := hp' 0
  have h1' := hp' 1
  have h2' := hp' 2
  simp only [coord] at h0 h1 h2 h0' h1' h2'
  rcases hcc with hc | hc | hc
  · exact Or.inl (sep_coord _ _ _ _ _ _ hc hb.1 hb'.1 h0.1 h0.2 h0'.1 h0'.2)
  · exact Or.inr (Or.inl (sep_coord _ _ _ _ _ _ hc hb.2.1 hb'.2.1 h1.1 h1.2 h1'.1 h1'.2))
  · exact Or.inr (Or.inr (sep_coord _ _ _ _ _ _ hc hb.2.2 hb'.2.2 h2.1 h2.2 h2'.1 h2'.2))

/-- **No common edge**: no pair of checks at `ℓ∞` distance at most 1 has one check in each window. -/
theorem no_common_edge (c c' b b' p p' : V3) (hcc : Const.D ≤ dist3 c c') (hb : dist3 b c ≤ 1)
    (hb' : dist3 b' c' ≤ 1) (hp : InWin b p) (hp' : InWin b' p') : ¬ linf (p - p') ≤ 1 := by
  have := indep_windows c c' b b' p p' hcc hb hb' hp hp'
  omega

/-- **`D = 4` fails**: blocks at distance 4 whose neighbourhood windows share a check. -/
theorem indep_fails_D4 :
    ∃ c c' b b' p : V3, 4 ≤ dist3 c c' ∧ dist3 b c ≤ 1 ∧ dist3 b' c' ≤ 1 ∧ InWin b p ∧ InWin b' p :=
  ⟨(0, 0, 0), (4, 0, 0), (1, 0, 0), (3, 0, 0), (80, 0, 0), by decide⟩

end QECD1
