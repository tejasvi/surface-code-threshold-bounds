import QECD1.Level1

/-!
# Lemma A in 3D: confinement (first part)

This ports the 2D `confine` (TwoD/LemmaA; Lemma A of the proof). Suppose block `c` is not
long. Then every check reachable through `F = E + C0` from a check of `c` lies within `ℓ∞` distance `L - 1 = 34` of
`c`, because the first exit to distance `L` would make `c` long. Only unit steps are used, so the argument is
dimension-free. The 3D part is the distance from a check to a block and its behaviour along an edge.

* `first_exit` (abstract): let `d` grow by at most 1 along each edge. If no walk inside `{d < L}` from `x0`
  (`d x0 = 0`) reaches `d = L` (`c` is not long), then every vertex reachable from `x0` has `d ≤ L - 1`.
* `distVB p c`: the `ℓ∞` distance from check `p ∈ ℤ³` to the checks `[c_i L, c_i L + L - 1]` of block `c` (`L = 35`).
* `distVB_lip`: along a unit step (`|p - p'|∞ ≤ 1`) it changes by at most 1.
* `blockOf_near`: a check within distance `L` of block `c` lies in a block of `N_1(c)`, i.e. `|blockOf p - c|∞ ≤ 1`.
* `confine3`: suppose block `c` is not long for the adjacency `adj` of `F`, whose steps are unit steps. Then every
  check reachable from a check of `c` is within distance 34 of `c`, and lies in a block of `N_1(c)`.
-/

namespace QECD1

/-- **First exit** (abstract form of Lemma A's first part). -/
theorem first_exit {V : Type} (adj : V → V → Prop) (d : V → ℕ) (hd : ∀ u v, adj u v → d v ≤ d u + 1) (L : ℕ)
    (hL : 1 ≤ L) (x0 : V) (hx0 : d x0 = 0)
    (hnl : ∀ y, Relation.ReflTransGen (fun u v => adj u v ∧ d u < L) x0 y → d y ≠ L) :
    ∀ y, Relation.ReflTransGen adj x0 y →
      d y ≤ L - 1 ∧ Relation.ReflTransGen (fun u v => adj u v ∧ d u < L) x0 y := by
  intro y hy
  induction hy with
  | refl => exact ⟨by omega, .refl⟩
  | tail _ hbc ih =>
    obtain ⟨hb, hpath⟩ := ih
    have hpath' := hpath.tail ⟨hbc, by omega⟩
    have h1 := hd _ _ hbc
    have h2 := hnl _ hpath'
    exact ⟨by omega, hpath'⟩

/-- Distance from an integer to the interval `[lo, hi]`. -/
def dist1 (x lo hi : ℤ) : ℕ := (max (lo - x) (max 0 (x - hi))).toNat

/-- `ℓ∞` distance from check `p` to the checks of block `c` (`L = 35`). -/
def distVB (p c : V3) : ℕ :=
  max (dist1 p.1 (c.1 * 35) (c.1 * 35 + 34))
    (max (dist1 p.2.1 (c.2.1 * 35) (c.2.1 * 35 + 34)) (dist1 p.2.2 (c.2.2 * 35) (c.2.2 * 35 + 34)))

/-- The block of a check. -/
def blockOf (p : V3) : V3 := (p.1 / 35, p.2.1 / 35, p.2.2 / 35)

theorem dist1_lip (x x' lo hi : ℤ) (h : (x - x').natAbs ≤ 1) : dist1 x' lo hi ≤ dist1 x lo hi + 1 := by
  simp only [dist1]
  omega

/-- **Along a unit step the distance to a block changes by at most 1.** -/
theorem distVB_lip (p p' c : V3) (h : linf (p - p') ≤ 1) : distVB p' c ≤ distVB p c + 1 := by
  simp only [linf, Prod.fst_sub, Prod.snd_sub, max_le_iff] at h
  have h1 := dist1_lip p.1 p'.1 (c.1 * 35) (c.1 * 35 + 34) h.1
  have h2 := dist1_lip p.2.1 p'.2.1 (c.2.1 * 35) (c.2.1 * 35 + 34) h.2.1
  have h3 := dist1_lip p.2.2 p'.2.2 (c.2.2 * 35) (c.2.2 * 35 + 34) h.2.2
  simp only [distVB]
  omega

theorem dist1_zero_of_mem (x lo hi : ℤ) (h1 : lo ≤ x) (h2 : x ≤ hi) : dist1 x lo hi = 0 := by
  simp only [dist1]
  omega

theorem div_near (x a : ℤ) (h : dist1 x (a * 35) (a * 35 + 34) ≤ 35) : (x / 35 - a).natAbs ≤ 1 := by
  simp only [dist1] at h
  omega

/-- **A check within distance `L` of block `c` lies in a block of `N_1(c)`.** -/
theorem blockOf_near (p c : V3) (h : distVB p c ≤ 35) : dist3 (blockOf p) c ≤ 1 := by
  simp only [distVB, max_le_iff] at h
  simp only [dist3, linf, blockOf, Prod.fst_sub, Prod.snd_sub, max_le_iff]
  exact ⟨div_near _ _ h.1, div_near _ _ h.2.1, div_near _ _ h.2.2⟩

/-- **Lemma A (first part) in 3D.** `adj` is the adjacency of `F` on checks; its steps are unit steps. `c` is not long:
no walk inside `{distVB · c < 35}` from the check `x0` of `c` reaches distance 35. -/
theorem confine3 (adj : V3 → V3 → Prop) (hunit : ∀ u v, adj u v → linf (u - v) ≤ 1) (c x0 : V3)
    (hx0 : distVB x0 c = 0)
    (hnl : ∀ y, Relation.ReflTransGen (fun u v => adj u v ∧ distVB u c < 35) x0 y → distVB y c ≠ 35) :
    ∀ y, Relation.ReflTransGen adj x0 y → distVB y c ≤ 34 ∧ dist3 (blockOf y) c ≤ 1 := by
  intro y hy
  have h := first_exit adj (fun p => distVB p c) (fun u v huv => distVB_lip u v c (hunit u v huv)) 35
    (by norm_num) x0 hx0 hnl y hy
  exact ⟨h.1, blockOf_near y c (by have := h.1; omega)⟩

end QECD1
