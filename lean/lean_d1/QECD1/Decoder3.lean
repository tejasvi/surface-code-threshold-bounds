import QECD1.Regions3

/-!
# The decoder S3' on the 3D code, and its validity

The 3D analogue of the 2D `S3/Decoder`, for any admissible stage-1
rule (`Stage13`):
* stage 1: `C_0`, the residual `D' = D + ∂C_0` (`residD3`), the flagged blocks (`flagSet3`);
* level 0: the `a0`-components `K` of the flagged blocks (`compOf`), with regions `region3 K r0`, `r0 = (a0 + 1)/2`.
  `K` is resolved (`Resolved3`) if `D'` has even parity on `K` (`parOf`) or its region reaches a rough side or covers
  the code (`reach3`); a resolved `K` gets a correction of `D'|K` (`restrict3`) inside its region;
* level 1: the same for the blocks of the unresolved level-0 components (`lev1Set3`), with adjacency `a1`;
* top: `Ω = D'` on the blocks of the unresolved level-1 components (`omega3`), corrected on the whole code;
* output `C = C_0 + ∑ C_K + ∑ C_K' + C_top` (`dec3`).

The minimum-weight solver is a parameter (`Solver3`). `dec3_valid`: the output is a valid correction for every
syndrome. It uses only the existence part of the solver, through `realizable_resolved`: the region of a component is
connected (`region3_conn`), so a resolved component's residual is realizable inside it.
-/

open Finset

namespace QECD1

open Classical

variable {T w h : ℕ}

/-- The `a`-component of `c` in `B`. -/
noncomputable def compOf (B : Finset V3) (a : ℕ) (c : V3) : Finset V3 := B.filter (fun y => SameComp B a c y)

theorem mem_compOf {B : Finset V3} {a : ℕ} {c y : V3} : y ∈ compOf B a c ↔ y ∈ B ∧ SameComp B a c y := by
  unfold compOf
  rw [Finset.mem_filter]

theorem compOf_sub (B : Finset V3) (a : ℕ) (c : V3) : compOf B a c ⊆ B := fun _ hy => (mem_compOf.1 hy).1

theorem self_mem_compOf {B : Finset V3} {a : ℕ} {c : V3} (hc : c ∈ B) : c ∈ compOf B a c :=
  mem_compOf.2 ⟨hc, .refl⟩

theorem compOf_eq_of_mem {B : Finset V3} {a : ℕ} {c y : V3} (hy : y ∈ compOf B a c) :
    compOf B a y = compOf B a c := by
  obtain ⟨_, hcy⟩ := mem_compOf.1 hy
  ext z
  simp only [mem_compOf]
  constructor
  · rintro ⟨hz, hyz⟩
    exact ⟨hz, hcy.trans hyz⟩
  · rintro ⟨hz, hcz⟩
    exact ⟨hz, (sameComp_symm B a hcy).trans hcz⟩

/-- Blocks of a component are chained inside the component by steps of distance at most `a`. -/
theorem compOf_chain {B : Finset V3} {a : ℕ} {c : V3} :
    ∀ c1 ∈ compOf B a c, ∀ c2 ∈ compOf B a c, Relation.ReflTransGen
      (fun x y => x ∈ compOf B a c ∧ y ∈ compOf B a c ∧ dist3 x y ≤ a) c1 c2 := by
  have hfrom : ∀ x, SameComp B a c x → Relation.ReflTransGen
      (fun x y => x ∈ compOf B a c ∧ y ∈ compOf B a c ∧ dist3 x y ≤ a) c x := by
    intro x hx
    induction hx with
    | refl => exact .refl
    | @tail b x hcb hbx ih =>
      exact .tail ih ⟨mem_compOf.2 ⟨hbx.1, hcb⟩, mem_compOf.2 ⟨hbx.2.1, hcb.tail hbx⟩, hbx.2.2⟩
  have hsymm : ∀ {x y}, Relation.ReflTransGen (fun x y => x ∈ compOf B a c ∧ y ∈ compOf B a c ∧ dist3 x y ≤ a) x y →
      Relation.ReflTransGen (fun x y => x ∈ compOf B a c ∧ y ∈ compOf B a c ∧ dist3 x y ≤ a) y x := by
    intro x y hxy
    induction hxy with
    | refl => exact .refl
    | tail _ hbc ih => exact .head ⟨hbc.2.1, hbc.1, by rw [dist3_comm]; exact hbc.2.2⟩ ih
  intro c1 hc1 c2 hc2
  exact (hsymm (hfrom c1 (mem_compOf.1 hc1).2)).trans (hfrom c2 (mem_compOf.1 hc2).2)

/-- The components of `B` under adjacency `a`. -/
noncomputable def comps3 (B : Finset V3) (a : ℕ) : Finset (Finset V3) := B.image (compOf B a)

theorem mem_comps3 {B : Finset V3} {a : ℕ} {K : Finset V3} : K ∈ comps3 B a ↔ ∃ c ∈ B, compOf B a c = K := by
  unfold comps3
  rw [Finset.mem_image]

/-- Among the components of `B`, the block `b ∈ B` lies exactly in its own. -/
theorem mem_comp_iff_eq {B : Finset V3} {a : ℕ} {K : Finset V3} (hK : K ∈ comps3 B a) {b : V3} (hb : b ∈ B) :
    b ∈ K ↔ K = compOf B a b := by
  obtain ⟨c, _, rfl⟩ := mem_comps3.1 hK
  constructor
  · intro hbK
    exact (compOf_eq_of_mem hbK).symm
  · intro hK'
    rw [hK']
    exact self_mem_compOf hb

/-- The reach condition at radius `r`: the region of `K` meets a rough side or covers the code. -/
def reach3 (T w h : ℕ) (r : ℕ) (K : Finset V3) : Prop :=
  (∃ v ∈ (region3 K r : Set (PVert3 T w h)), v.2.2 = 0 ∨ v.2.2 = Fin.last h) ∨
    ∀ v : PVert3 T w h, v ∈ (region3 K r : Set (PVert3 T w h))

/-- Restriction of a syndrome to the checks of the blocks of `K`. -/
noncomputable def restrict3 (K : Finset V3) (S : PVert3 T w h → ZMod 2) : PVert3 T w h → ZMod 2 :=
  fun v => if blockOf3 v ∈ K then S v else 0

/-- The parity of a syndrome on the checks of block `b`. -/
noncomputable def parOf (S : PVert3 T w h → ZMod 2) (b : V3) : ZMod 2 :=
  ∑ v ∈ Finset.univ.filter (fun v : PVert3 T w h => blockOf3 v = b), S v

/-- The parity on the blocks of `K` is the total of the restricted syndrome. -/
theorem sum_restrict3 (K : Finset V3) (S : PVert3 T w h → ZMod 2) :
    ∑ v, restrict3 K S v = ∑ b ∈ K, parOf S b := by
  unfold restrict3 parOf
  rw [← Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun v : PVert3 T w h => blockOf3 v ∈ K))
    (t := K) (g := blockOf3) (fun v hv => (Finset.mem_filter.1 hv).2) S]
  refine Finset.sum_congr rfl fun b hb => ?_
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro hv
    exact ⟨hv ▸ hb, hv⟩

/-- **A resolved component's residual is realizable inside its region.** -/
theorem realizable_resolved {B : Finset V3} {a : ℕ} {c : V3}
    (hBc : ∀ b ∈ B, ∃ v : PVert3 T w h, blockOf3 v = b) {S : PVert3 T w h → ZMod 2}
    (hres : Resolved3 (parOf S) (reach3 T w h ((a + 1) / 2)) (compOf B a c)) :
    Realizable3 (region3 (compOf B a c) ((a + 1) / 2)) (restrict3 (compOf B a c) S) := by
  have hconn : Conn3 (region3 (compOf B a c) ((a + 1) / 2) : Set (PVert3 T w h)) :=
    region3_conn (by omega) (fun b hb => hBc b (compOf_sub B a c hb)) compOf_chain
  have hsupp : ∀ v, restrict3 (compOf B a c) S v ≠ 0 → v ∈ (region3 (compOf B a c) ((a + 1) / 2) :
      Set (PVert3 T w h)) := by
    intro v hv
    unfold restrict3 at hv
    split_ifs at hv with hvK
    · exact ⟨blockOf3 v, hvK, by rw [dist3_self]; exact Nat.zero_le _⟩
    · exact absurd rfl hv
  rcases hres with heven | ⟨r, hr, hrough⟩ | hall
  · exact realizable_of_even hconn hsupp (by rw [sum_restrict3]; exact heven)
  · exact realizable_of_rough hconn hr hrough hsupp
  · exact realizable_of_rough hconn (hall (0, 0, 0)) (Or.inl rfl) hsupp

/-- A minimum-weight solver: on a region `U` and a syndrome `S` realizable inside `U`, it returns an edge set inside
`U` with syndrome `S` and minimum weight for its weights `wt`. -/
structure Solver3 (T w h : ℕ) where
  solve : Set (PVert3 T w h) → (PVert3 T w h → ZMod 2) → (PEdge3 T w h → ZMod 2)
  wt : PEdge3 T w h → ℝ
  correct : ∀ U S, Realizable3 U S → psyn3 (solve U S) = S
  inside : ∀ U S, Realizable3 U S → Inside3 U (solve U S)
  minimal : ∀ U S X, Inside3 U X → psyn3 X = S →
    (∑ e, if solve U S e ≠ 0 then wt e else 0) ≤ ∑ e, if X e ≠ 0 then wt e else 0

/-- The radius of the level-0 regions. -/
def r0 : ℕ := (Const.a0 + 1) / 2

/-- The radius of the level-1 regions. -/
def r1 : ℕ := (Const.a1 + 1) / 2

/-- The residual `D' = D + ∂C_0` as a function of the syndrome. -/
def residD3 (S : Stage13 T w h) (D : PVert3 T w h → ZMod 2) : PVert3 T w h → ZMod 2 := D + psyn3 (S.C0 D)

/-- The flagged blocks of a residual. -/
noncomputable def flagSet3 (Dp : PVert3 T w h → ZMod 2) : Finset V3 :=
  (latBlocks T w h).filter (fun c => ∃ v, blockOf3 v = c ∧ Dp v ≠ 0)

/-- The level-1 blocks: the flagged blocks whose level-0 component is unresolved. -/
noncomputable def lev1Set3 (Dp : PVert3 T w h → ZMod 2) : Finset V3 :=
  level1Set3 (flagSet3 Dp) (parOf Dp) (reach3 T w h r0)

/-- The top-level syndrome `Ω`: `D'` on the blocks of the unresolved level-1 components. -/
noncomputable def omega3 (Dp : PVert3 T w h → ZMod 2) : PVert3 T w h → ZMod 2 := fun v =>
  if blockOf3 v ∈ lev1Set3 Dp ∧ ¬ Resolved3 (parOf Dp) (reach3 T w h r1) (compOf (lev1Set3 Dp) Const.a1 (blockOf3 v))
  then Dp v else 0

/-- The corrections of the resolved components of `B` under adjacency `a`. -/
noncomputable def levelSum3 (Z : Solver3 T w h) (Dp : PVert3 T w h → ZMod 2) (B : Finset V3) (a : ℕ) :
    PEdge3 T w h → ZMod 2 :=
  ∑ K ∈ (comps3 B a).filter (Resolved3 (parOf Dp) (reach3 T w h ((a + 1) / 2))),
    Z.solve (region3 K ((a + 1) / 2)) (restrict3 K Dp)

/-- **The decoder S3' on the 3D code**: stage-1 rule `S`, minimum-weight solver `Z`, adjacencies `a0`, `a1`. -/
noncomputable def dec3 (S : Stage13 T w h) (Z : Solver3 T w h) (D : PVert3 T w h → ZMod 2) : PEdge3 T w h → ZMod 2 :=
  S.C0 D + levelSum3 Z (residD3 S D) (flagSet3 (residD3 S D)) Const.a0 +
    levelSum3 Z (residD3 S D) (lev1Set3 (residD3 S D)) Const.a1 + Z.solve Set.univ (omega3 (residD3 S D))

theorem psyn3_sum {ι : Type} (s : Finset ι) (X : ι → PEdge3 T w h → ZMod 2) :
    psyn3 (∑ i ∈ s, X i) = ∑ i ∈ s, psyn3 (X i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact psyn3_zero
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, psyn3_add, ih]

theorem flagSet3_blocks (Dp : PVert3 T w h → ZMod 2) : ∀ b ∈ flagSet3 Dp, ∃ v : PVert3 T w h, blockOf3 v = b := by
  intro b hb
  obtain ⟨v, hv, _⟩ := (Finset.mem_filter.1 hb).2
  exact ⟨v, hv⟩

theorem lev1Set3_blocks (Dp : PVert3 T w h → ZMod 2) : ∀ b ∈ lev1Set3 Dp, ∃ v : PVert3 T w h, blockOf3 v = b :=
  fun b hb => flagSet3_blocks Dp b (level1Set3_sub _ _ _ hb)

theorem psyn3_levelSum3 (Z : Solver3 T w h) (Dp : PVert3 T w h → ZMod 2) (B : Finset V3) (a : ℕ)
    (hBc : ∀ b ∈ B, ∃ v : PVert3 T w h, blockOf3 v = b) :
    psyn3 (levelSum3 Z Dp B a) =
      ∑ K ∈ (comps3 B a).filter (Resolved3 (parOf Dp) (reach3 T w h ((a + 1) / 2))), restrict3 K Dp := by
  rw [levelSum3, psyn3_sum]
  refine Finset.sum_congr rfl fun K hK => ?_
  obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hK
  obtain ⟨c, hc, rfl⟩ := mem_comps3.1 hK1
  exact Z.correct _ _ (realizable_resolved hBc hres)

/-- The components of `B` partition `B` (as indicator sums of a restricted syndrome). -/
theorem sum_restrict_comps3 (B : Finset V3) (a : ℕ) (P : Finset V3 → Prop) (Dp : PVert3 T w h → ZMod 2)
    (v : PVert3 T w h) :
    ∑ K ∈ (comps3 B a).filter P, restrict3 K Dp v =
      if blockOf3 v ∈ B ∧ P (compOf B a (blockOf3 v)) then Dp v else 0 := by
  simp only [restrict3]
  split_ifs with hv
  · obtain ⟨hb, hP⟩ := hv
    rw [Finset.sum_eq_single (compOf B a (blockOf3 v))]
    · simp [self_mem_compOf hb]
    · intro K hK hne
      rw [Finset.mem_filter] at hK
      have : blockOf3 v ∉ K := fun hvK => hne ((mem_comp_iff_eq hK.1 hb).1 hvK)
      simp [this]
    · intro hnot
      exact absurd (Finset.mem_filter.2 ⟨mem_comps3.2 ⟨_, hb, rfl⟩, hP⟩) hnot
  · refine Finset.sum_eq_zero fun K hK => ?_
    rw [Finset.mem_filter] at hK
    have : blockOf3 v ∉ K := by
      intro hvK
      obtain ⟨c, _, rfl⟩ := mem_comps3.1 hK.1
      have hb : blockOf3 v ∈ B := compOf_sub B a c hvK
      exact hv ⟨hb, by rw [compOf_eq_of_mem hvK]; exact hK.2⟩
    simp [this]

/-- The whole code is connected. -/
theorem conn3_univ : Conn3 (Set.univ : Set (PVert3 T w h)) := by
  intro u _ v _
  have hbig : ∀ x : PVert3 T w h, x ∈ (box3 (0, 0, 0) (T + w + h) : Set (PVert3 T w h)) := by
    intro x
    rw [mem_box3_iff]
    simp only
    have h1 := x.1.isLt
    have h2 := x.2.1.isLt
    have h3 := x.2.2.isLt
    omega
  exact reach3_mono (fun _ _ => Set.mem_univ _) (box3_conn _ _ u (hbig u) v (hbig v))

/-- **Validity** (on the 3D code): for every admissible stage-1 rule and every minimum-weight solver, the
output of S3' is a valid correction for every syndrome. -/
theorem dec3_valid (S : Stage13 T w h) (Z : Solver3 T w h) (D : PVert3 T w h → ZMod 2) :
    psyn3 (dec3 S Z D) = D := by
  set Dp := residD3 S D with hDp
  have htop : psyn3 (Z.solve Set.univ (omega3 Dp)) = omega3 Dp :=
    Z.correct _ _ (realizable_of_rough conn3_univ (Set.mem_univ (0, 0, 0)) (Or.inl rfl) fun v _ => Set.mem_univ v)
  have hpart : ∀ v, (∑ K ∈ (comps3 (flagSet3 Dp) Const.a0).filter
        (Resolved3 (parOf Dp) (reach3 T w h ((Const.a0 + 1) / 2))), restrict3 K Dp v) +
      (∑ K ∈ (comps3 (lev1Set3 Dp) Const.a1).filter
        (Resolved3 (parOf Dp) (reach3 T w h ((Const.a1 + 1) / 2))), restrict3 K Dp v) +
      omega3 Dp v = Dp v := by
    intro v
    rw [sum_restrict_comps3, sum_restrict_comps3]
    simp only [omega3]
    by_cases hv : Dp v = 0
    · simp [hv]
    · have hfl : blockOf3 v ∈ flagSet3 Dp :=
        Finset.mem_filter.2 ⟨blockOf3_mem_latBlocks v, v, rfl, hv⟩
      have hcl : compOf (flagSet3 Dp) Const.a0 (blockOf3 v) = clusterOf (flagSet3 Dp) (blockOf3 v) := rfl
      by_cases h0 : Resolved3 (parOf Dp) (reach3 T w h r0) (clusterOf (flagSet3 Dp) (blockOf3 v))
      · have hn1 : blockOf3 v ∉ lev1Set3 Dp := fun h1 => (mem_level1Set3.1 h1).2 h0
        have h0' : Resolved3 (parOf Dp) (reach3 T w h ((Const.a0 + 1) / 2))
            (compOf (flagSet3 Dp) Const.a0 (blockOf3 v)) := h0
        simp [hfl, h0', hn1]
      · have h1 : blockOf3 v ∈ lev1Set3 Dp := mem_level1Set3.2 ⟨hfl, h0⟩
        have h0' : ¬ Resolved3 (parOf Dp) (reach3 T w h ((Const.a0 + 1) / 2))
            (compOf (flagSet3 Dp) Const.a0 (blockOf3 v)) := h0
        by_cases hr1 : Resolved3 (parOf Dp) (reach3 T w h r1) (compOf (lev1Set3 Dp) Const.a1 (blockOf3 v))
        · have hr1' : Resolved3 (parOf Dp) (reach3 T w h ((Const.a1 + 1) / 2))
              (compOf (lev1Set3 Dp) Const.a1 (blockOf3 v)) := hr1
          simp [hfl, h0', h1, hr1, hr1']
        · have hr1' : ¬ Resolved3 (parOf Dp) (reach3 T w h ((Const.a1 + 1) / 2))
              (compOf (lev1Set3 Dp) Const.a1 (blockOf3 v)) := hr1
          simp [hfl, h0', h1, hr1, hr1']
  have hC0 : ∀ v, psyn3 (S.C0 D) v = D v + Dp v := by
    intro v
    simp only [hDp, residD3, Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  show psyn3 (S.C0 D + levelSum3 Z Dp (flagSet3 Dp) Const.a0 + levelSum3 Z Dp (lev1Set3 Dp) Const.a1 +
    Z.solve Set.univ (omega3 Dp)) = D
  rw [psyn3_add, psyn3_add, psyn3_add, psyn3_levelSum3 Z Dp _ _ (flagSet3_blocks Dp),
    psyn3_levelSum3 Z Dp _ _ (lev1Set3_blocks Dp), htop]
  funext v
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [hC0 v]
  have hp := hpart v
  calc D v + Dp v + ∑ K ∈ (comps3 (flagSet3 Dp) Const.a0).filter
        (Resolved3 (parOf Dp) (reach3 T w h ((Const.a0 + 1) / 2))), restrict3 K Dp v +
      ∑ K ∈ (comps3 (lev1Set3 Dp) Const.a1).filter
        (Resolved3 (parOf Dp) (reach3 T w h ((Const.a1 + 1) / 2))), restrict3 K Dp v + omega3 Dp v
      = D v + Dp v + Dp v := by rw [← hp]; ring
    _ = D v := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The decoder's stage-1 residual for the syndrome of `E` is the residual of `E + C_0`. -/
theorem residD3_eq (S : Stage13 T w h) (E : PEdge3 T w h → ZMod 2) : residD3 S (psyn3 E) = psyn3 (S.Fcfg E) :=
  (S.psyn3_Fcfg E).symm

theorem flagSet3_Fcfg (S : Stage13 T w h) (E : PEdge3 T w h → ZMod 2) : flagSet3 (psyn3 (S.Fcfg E)) = S.flSet E := by
  ext c
  simp only [flagSet3, Stage13.flSet, Finset.mem_filter, Stage13.flagged]

theorem parOf_psyn3 (X : PEdge3 T w h → ZMod 2) : parOf (psyn3 X) = blockPar3 X := rfl

/-- The decoder's flagged blocks are `flSet` of `Cover3`. -/
theorem flagSet3_eq (S : Stage13 T w h) (E : PEdge3 T w h → ZMod 2) : flagSet3 (residD3 S (psyn3 E)) = S.flSet E := by
  rw [residD3_eq, flagSet3_Fcfg]

/-- The decoder's level-1 blocks are `levSet` of `Cover3`, with the reach rule at radius `r0`. -/
theorem lev1Set3_eq (S : Stage13 T w h) (E : PEdge3 T w h → ZMod 2) :
    lev1Set3 (residD3 S (psyn3 E)) = S.levSet (reach3 T w h r0) E := by
  rw [lev1Set3, residD3_eq, flagSet3_Fcfg, parOf_psyn3]
  rfl

/-- The residual `E + C` of the decoder has zero syndrome. -/
theorem psyn3_resid_dec3 (S : Stage13 T w h) (Z : Solver3 T w h) (E : PEdge3 T w h → ZMod 2) :
    psyn3 (E + dec3 S Z (psyn3 E)) = 0 := by
  rw [psyn3_add, dec3_valid]
  funext v
  exact CharTwo.add_self_eq_zero _

end QECD1
