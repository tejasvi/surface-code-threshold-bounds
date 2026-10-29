import QECD1.DecoderDefs3

/-!
# A3 on the 3D code from Lemma A (2D `cluster_eq_of_reach`)

A block is long if an `X`-walk inside `{distVB · c < 35}` from one of its checks reaches distance 35. Its negation is
`NotLong3`, which is exactly the hypothesis of `confine_model`. The bad blocks include the long ones.

`a3_code3`: if every block outside `F` is not long, then `X`-connected blocks of `F` lie in one `a0`-component of `F`.
The proof follows the 2D proof:
* walk along the `X`-path; each step moves to a block at distance `≤ 1` (`blockOf3_step`);
* while the blocks stay in `F`, they stay in the cluster;
* at the first block `c'` outside `F`, the rest of the path stays in `N_1(c')`, by Lemma A (`confine_model`);
* so the final bad block is within `2 ≤ a0` of the last bad block before `c'`.

`gen_skel3_final` is the deterministic lemma on the 3D code with A3 proved. Its hypotheses are definitional or
structural:
* A2 (odd checks lie in flagged blocks, i.e. the flagged set of `psyn3 X`);
* the bad blocks contain the long blocks and the declared blocks;
* the level-1 blocks are `level1Set3`;
* the strips (no declared block in the family's clusters, no reach);
* the family is unresolved.
-/

namespace QECD1

open Classical

variable {T w h : ℕ}

theorem distVB_blockOf (p : V3) : distVB p (blockOf p) = 0 := by
  simp only [distVB, blockOf]
  rw [dist1_zero_of_mem _ _ _ (by omega) (by omega), dist1_zero_of_mem _ _ _ (by omega) (by omega),
    dist1_zero_of_mem _ _ _ (by omega) (by omega)]
  rfl

/-- An `X`-step moves to a block at distance at most 1. -/
theorem blockOf3_step {X : PEdge3 T w h → ZMod 2} {u v : PVert3 T w h} (huv : Fadj X u v) :
    dist3 (blockOf3 u) (blockOf3 v) ≤ 1 := by
  have h1 := distVB_lip u.toV3 v.toV3 (blockOf u.toV3) (Fadj_unit X huv)
  rw [distVB_blockOf] at h1
  have h2 := blockOf_near v.toV3 (blockOf u.toV3) (by omega)
  rw [dist3_comm] at h2
  exact h2

/-- Block `c` is not long: no `X`-walk inside `{distVB · c < 35}` from a check of `c` reaches distance 35. -/
def NotLong3 (X : PEdge3 T w h → ZMod 2) (c : V3) : Prop :=
  ∀ x0 : PVert3 T w h, blockOf3 x0 = c →
    ∀ y, Relation.ReflTransGen (fun u v => Fadj X u v ∧ distVB u.toV3 c < 35) x0 y → distVB y.toV3 c ≠ 35

/-- **A3 on the 3D code** (2D `cluster_eq_of_reach`). -/
theorem a3_code3 (X : PEdge3 T w h → ZMod 2) (F : Finset V3) (hlong : ∀ c, c ∉ F → NotLong3 X c) :
    ∀ u v : PVert3 T w h, Relation.ReflTransGen (Fadj X) u v → blockOf3 u ∈ F → blockOf3 v ∈ F →
      SameComp F Const.a0 (blockOf3 u) (blockOf3 v) := by
  intro u v huv hu hv
  have h1a0 : (1 : ℕ) ≤ Const.a0 := by decide
  have h2a0 : (2 : ℕ) ≤ Const.a0 := by decide
  have claim : ∀ y, Relation.ReflTransGen (Fadj X) u y →
      (blockOf3 y ∈ F ∧ SameComp F Const.a0 (blockOf3 u) (blockOf3 y)) ∨
      ∃ c', c' ∉ F ∧ (∃ k, k ∈ F ∧ SameComp F Const.a0 (blockOf3 u) k ∧ dist3 k c' ≤ 1) ∧
        ∃ a, blockOf3 a = c' ∧ Relation.ReflTransGen (Fadj X) a y := by
    intro y hy
    induction hy with
    | refl => exact Or.inl ⟨hu, .refl⟩
    | @tail b y' _ hstep ih =>
      have hby := blockOf3_step hstep
      rcases ih with ⟨hbF, hub⟩ | ⟨c', hc', hk, a, ha, har⟩
      · by_cases hyF : blockOf3 y' ∈ F
        · exact Or.inl ⟨hyF, hub.tail ⟨hbF, hyF, le_trans hby h1a0⟩⟩
        · exact Or.inr ⟨blockOf3 y', hyF, ⟨blockOf3 b, hbF, hub, hby⟩, y', rfl, .refl⟩
      · exact Or.inr ⟨c', hc', hk, a, ha, har.tail hstep⟩
  rcases claim v huv with ⟨_, huv'⟩ | ⟨c', hc', ⟨k, hkF, huk, hkc⟩, a, ha, har⟩
  · exact huv'
  · have hx0 : distVB a.toV3 c' = 0 := by
      rw [← ha]
      exact distVB_blockOf _
    have hconf := (confine_model X c' a hx0 (hlong c' hc' a ha) v har).2
    have t := dist3_triangle k c' (blockOf3 v)
    rw [dist3_comm c' (blockOf3 v)] at t
    have hkv : dist3 k (blockOf3 v) ≤ Const.a0 := by omega
    exact huk.tail ⟨hkF, hv, hkv⟩

/-- **The deterministic lemma on the 3D code, with A3 proved.** The hypotheses:
* A2 (`hA2`): an odd check of `X` lies in a flagged block (`Fl` is the flagged set of the residual `psyn3 X`);
* the bad blocks contain the long blocks (`hlong`) and the declared blocks (`hdeclF`, convention (i));
* the level-1 blocks are `level1Set3 Fl (blockPar3 X) reach0` (`hL`);
* the strips: the family's clusters contain no declared block (`hnodecl`), and the level-0 components in the clusters
  meeting the family's level-1 component do not reach (`hnoreach`);
* the family is unresolved at level 1 (`hunres1`). -/
theorem gen_skel3_final (X : PEdge3 T w h → ZMod 2) (F Fl L : Finset V3) (hFl : Fl ⊆ F)
    (reach0 reach1 : Finset V3 → Prop) (hL : L = level1Set3 Fl (blockPar3 X) reach0) (ny : ℕ)
    (hh : h + 1 = ny * 35)
    (hA2 : ∀ v : PVert3 T w h, psyn3 X v ≠ 0 → blockOf3 v ∈ Fl)
    (hlong : ∀ c, c ∉ F → NotLong3 X c)
    (hdeclF : ∀ v : PVert3 T w h, declared3 ny (blockOf3 v) → blockOf3 v ∈ F)
    {e x : V3} (he : e ∈ L) (hx : x ∈ L) (hfam : InFamily3 F L e x)
    (hnodecl : ∀ r ∈ L, InFamily3 F L e r → ∀ b ∈ clusterOf F r, ¬ declared3 ny b)
    (hnoreach : ∀ b ∈ Fl, (∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) →
      ¬ reach0 (clusterOf Fl b))
    (hunres1 : ¬ Resolved3 (blockPar3 X) reach1 (L.filter (fun b => SameComp L Const.a1 e b))) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ famF F L e) ∧
      (keyBlocks e k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length :=
  gen_skel3_decoder3_defs X F Fl L hFl reach0 reach1 hL ny hh hA2 (a3_code3 X F hlong) hdeclF he hx hfam hnodecl
    hnoreach hunres1

end QECD1
