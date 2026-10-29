import QECD1.Params

/-!
# The rooting rule (R0) and the single cover offset in `A1`, `Sw` and `J`

**(R0)** (`RootsActual`): every route root of a family is an actual block of an odd level-0 component, never a
selected cover. This applies to the landing root, to the root entered by each link, and to the witness part's root
`e*`. Selected blocks cover the blocks of their cluster within `D - 1` (`Covers`).

Under (R0) each of `A1`, `Sw` and `J` contains exactly one cover offset `D - 1`:

* `link_le_A1`: from the selected block `s` covering the exit block `b` to the next root `b'` (an actual block
  within `a1` of `b`), the link offset has `|b' - s|∞ ≤ A1 = (D - 1) + a1`;
* `witness_ge_Sw`: from the root `e*` (the odd block itself) to the last selected block `sw` of the witness walk,
  which covers the witness block `w` of another level-1 component (`|w - e*|∞ ≥ a1 + 1`), `|sw - e*|∞ ≥ Sw`; the
  covered end is the witness end;
* `landing_ge_J`: from the exit cover to the next landing root (an actual block more than `a1` from the exit
  block), `|r' - s|∞ ≥ J`.

The bounds are sharp (`link_le_A1_sharp`, `witness_ge_Sw_sharp`). They FAIL when a root is a selected cover of the
odd block: `link_cover_root_28` gives a link offset `28 > A1`, and `witness_cover_root_13` a span `13 < Sw`. With
those values the transfer ratio diverges.
-/

namespace QECD1

theorem linf_sub_comm (a b : V3) : linf (a - b) = linf (b - a) := by
  simp only [linf, Prod.fst_sub, Prod.snd_sub]
  have h1 : (a.1 - b.1).natAbs = (b.1 - a.1).natAbs := by omega
  have h2 : (a.2.1 - b.2.1).natAbs = (b.2.1 - a.2.1).natAbs := by omega
  have h3 : (a.2.2 - b.2.2).natAbs = (b.2.2 - a.2.2).natAbs := by omega
  rw [h1, h2, h3]

/-- Triangle inequality for the `ℓ∞` distance. -/
theorem linf_sub_le (a b c : V3) : linf (a - c) ≤ linf (a - b) + linf (b - c) := by
  simp only [linf, Prod.fst_sub, Prod.snd_sub]
  have x1 := le_max_left (a.1 - b.1).natAbs (max (a.2.1 - b.2.1).natAbs (a.2.2 - b.2.2).natAbs)
  have x2 := le_max_left (a.2.1 - b.2.1).natAbs (a.2.2 - b.2.2).natAbs
  have x2' := le_max_right (a.1 - b.1).natAbs (max (a.2.1 - b.2.1).natAbs (a.2.2 - b.2.2).natAbs)
  have x3 := le_max_right (a.2.1 - b.2.1).natAbs (a.2.2 - b.2.2).natAbs
  have y1 := le_max_left (b.1 - c.1).natAbs (max (b.2.1 - c.2.1).natAbs (b.2.2 - c.2.2).natAbs)
  have y2 := le_max_left (b.2.1 - c.2.1).natAbs (b.2.2 - c.2.2).natAbs
  have y2' := le_max_right (b.1 - c.1).natAbs (max (b.2.1 - c.2.1).natAbs (b.2.2 - c.2.2).natAbs)
  have y3 := le_max_right (b.2.1 - c.2.1).natAbs (b.2.2 - c.2.2).natAbs
  refine max_le ?_ (max_le ?_ ?_) <;> omega

/-- `s` covers `b`: the selected block `s` lies within `D - 1` of the block `b`. -/
def Covers (s b : V3) : Prop := linf (s - b) ≤ Const.D - 1

instance (s b : V3) : Decidable (Covers s b) := inferInstanceAs (Decidable (linf (s - b) ≤ Const.D - 1))

/-- **(R0)**, the rooting rule of the 3D deterministic lemma: every root in `roots` (the landing root, the roots
entered by links, the witness part's root) is an actual block of an odd level-0 component (`odd0`). -/
def RootsActual (odd0 : Set V3) (roots : List V3) : Prop := ∀ r ∈ roots, r ∈ odd0

/-- **Links, one cover offset**: `s` covers the exit block `b`, and the next root `b'` (an actual block by (R0))
lies within `a1` of `b`. -/
theorem link_le_A1 (s b b' : V3) (hs : Covers s b) (hb : linf (b - b') ≤ Const.a1) :
    linf (b' - s) ≤ Const.A1 := by
  have h := linf_sub_le b' b s
  rw [linf_sub_comm b' b, linf_sub_comm b s] at h
  unfold Covers at hs
  simp only [Const.A1] at *
  omega

/-- **Witness span, one cover offset**: the root `e` is the odd block itself, the witness block `w` lies in another
level-1 component (`|w - e|∞ ≥ a1 + 1`), and the last selected block `sw` of the witness walk covers `w`. -/
theorem witness_ge_Sw (e sw w : V3) (hw : Const.a1 + 1 ≤ linf (w - e)) (hc : Covers sw w) :
    Const.Sw ≤ linf (sw - e) := by
  have h := linf_sub_le w sw e
  rw [linf_sub_comm w sw] at h
  unfold Covers at hc
  simp only [Const.Sw, Const.D_val, Const.a1] at *
  omega

/-- **Landing, one cover offset**: `s` covers the exit block `b`, and the next landing root `r'` (an actual block by
(R0)) lies more than `a1` from `b`. -/
theorem landing_ge_J (s b r' : V3) (hs : Covers s b) (hr : Const.a1 + 1 ≤ linf (r' - b)) :
    Const.J ≤ linf (r' - s) := by
  have h := linf_sub_le r' s b
  unfold Covers at hs
  simp only [Const.J, Const.D_val, Const.a1] at *
  omega

/-- `link_le_A1` is sharp. -/
theorem link_le_A1_sharp :
    ∃ s b b' : V3, Covers s b ∧ linf (b - b') ≤ Const.a1 ∧ linf (b' - s) = Const.A1 :=
  ⟨(0, 0, 0), (4, 0, 0), (24, 0, 0), by decide⟩

/-- `witness_ge_Sw` is sharp. -/
theorem witness_ge_Sw_sharp :
    ∃ e sw w : V3, Const.a1 + 1 ≤ linf (w - e) ∧ Covers sw w ∧ linf (sw - e) = Const.Sw :=
  ⟨(0, 0, 0), (17, 0, 0), (21, 0, 0), by decide⟩

/-- **Without (R0) the link range fails**: if the next root were a selected cover `c` of the actual block `b'`, the
link offset could be `2 (D - 1) + a1 = 28 > A1`. -/
theorem link_cover_root_28 :
    ∃ s b b' c : V3, Covers s b ∧ linf (b - b') ≤ Const.a1 ∧ Covers c b' ∧ linf (c - s) = 28 ∧
      Const.A1 < linf (c - s) :=
  ⟨(0, 0, 0), (4, 0, 0), (24, 0, 0), (28, 0, 0), by decide⟩

/-- **Without (R0) the witness span fails**: if the witness part were rooted at a selected cover `c` of the odd
block `e`, the span could be `a1 + 1 - 2 (D - 1) = 13 < Sw`. -/
theorem witness_cover_root_13 :
    ∃ e c sw w : V3, Const.a1 + 1 ≤ linf (w - e) ∧ Covers sw w ∧ Covers c e ∧ linf (sw - c) = 13 ∧
      linf (sw - c) < Const.Sw :=
  ⟨(0, 0, 0), (4, 0, 0), (17, 0, 0), (21, 0, 0), by decide⟩

end QECD1
