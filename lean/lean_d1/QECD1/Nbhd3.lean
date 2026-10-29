import QECD1.ExchangeX3

/-!
# Neighbourhoods of blocks and independence on the 3D code

The bad event of block `c` depends only on the edges with an end in the window of a block of `N_1(c)` (`Nbhd3 c`).


* `nbhd3_disjoint`: for `D`-separated blocks these edge sets are disjoint (`no_common_edge`, `ends_adjacent`). So the
  two bad events are independent under product noise.
* `skel_nbhd_disjoint`: a list of pairwise `D`-separated blocks has pairwise disjoint neighbourhoods. The counted blocks
  of a good skeleton are such a list (`gen_skel3_final`). The probability that all of them are bad is therefore the
  product of the single-block probabilities, each at most `ε` by (H_eps).
-/

namespace QECD1

variable {T w h : ℕ}

open Classical

/-- The edges on which the bad event of block `c` depends: those with an end in the window of a block of `N_1(c)`. -/
noncomputable def Nbhd3 (c : V3) : Finset (PEdge3 T w h) :=
  Finset.univ.filter (fun e => ∃ v ∈ e.ends, ∃ b : V3, dist3 b c ≤ 1 ∧ InWin b v.toV3)

/-- **`D`-separated blocks have disjoint neighbourhoods.** -/
theorem nbhd3_disjoint {c c' : V3} (hcc : Const.D ≤ dist3 c c') :
    Disjoint (Nbhd3 (T := T) (w := w) (h := h) c) (Nbhd3 c') := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨v, hv, b, hb, hvw⟩ := (Finset.mem_filter.1 he).2
  obtain ⟨v', hv', b', hb', hvw'⟩ := (Finset.mem_filter.1 he').2
  exact no_common_edge c c' b b' v.toV3 v'.toV3 hcc hb hb' hvw hvw' (ends_adjacent e hv hv')

/-- **Pairwise `D`-separated blocks have pairwise disjoint neighbourhoods**, e.g. the counted blocks of a good
skeleton. -/
theorem skel_nbhd_disjoint {B : List V3} (hB : B.Pairwise (fun a b => Const.D ≤ dist3 a b)) :
    B.Pairwise (fun a b => Disjoint (Nbhd3 (T := T) (w := w) (h := h) a) (Nbhd3 b)) :=
  hB.imp fun hab => nbhd3_disjoint hab

end QECD1
