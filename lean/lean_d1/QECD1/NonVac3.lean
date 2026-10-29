import QECD1.FamilyRestrict3

/-!
# The hypotheses of the main deterministic theorem are satisfiable

The example is one cluster of bad blocks along the t-axis, `0, 4, 8, 12, 16, 20, 21`. Its two ends `e = 0` and
`w = 21` are flagged, of odd residual parity, and level-1, 21 blocks apart. All hypotheses of
`gen_skel3_parity_family` hold:
* the level-0 components `{e}`, `{w}` are odd, since `21 > a0`;
* the cluster is even (`1 + 1`);
* the level-1 component `{e}` of `e` is odd, since `21 > a1 = 20`;
* the level-1 blocks of the cluster, `{e, w}`, have even total parity;
* the exit is `e` itself.

`main_hyps_nonvac` states this, and `main_nonvac` applies the theorem to the example and obtains a good skeleton. So
the main theorem is not vacuous, and the decoder facts are consistent with each other.
-/

namespace QECD1

open Classical

/-- If every step at range `a` within `F` from `e` stays at `e`, the component of `e` is `{e}`. -/
theorem sameComp_trapped {F : Finset V3} {a : ℕ} {e y : V3} (htrap : ∀ z, AdjIn F a e z → z = e)
    (h : SameComp F a e y) : y = e := by
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih =>
    subst ih
    exact htrap c hbc

/-- The example's bad blocks, along the t-axis. -/
def exF : Finset V3 := {(0, 0, 0), (4, 0, 0), (8, 0, 0), (12, 0, 0), (16, 0, 0), (20, 0, 0), (21, 0, 0)}

/-- The example's flagged and level-1 blocks: the two ends, 21 apart. -/
def exL : Finset V3 := {(0, 0, 0), (21, 0, 0)}

/-- Odd residual parity exactly at the two ends. -/
def exPar (b : V3) : ZMod 2 := if b = (0, 0, 0) ∨ b = (21, 0, 0) then 1 else 0

theorem exL_sub : exL ⊆ exF := by decide

theorem ex_dist : dist3 ((0 : ℤ), (0 : ℤ), (0 : ℤ)) (21, 0, 0) = 21 := by decide

theorem ex_dist' : dist3 ((21 : ℤ), (0 : ℤ), (0 : ℤ)) (0, 0, 0) = 21 := by decide

/-- The two ends are alone in their components at any range up to 20. -/
theorem ex_trapped {a : ℕ} (ha : a ≤ 20) {e y : V3} (he : e ∈ exL) (h : SameComp exL a e y) : y = e := by
  refine sameComp_trapped (fun z hz => ?_) h
  obtain ⟨_, hz, hd⟩ := hz
  simp only [exL, Finset.mem_insert, Finset.mem_singleton] at he hz
  rcases he with rfl | rfl <;> rcases hz with rfl | rfl
  · rfl
  · rw [ex_dist] at hd
    omega
  · rw [ex_dist'] at hd
    omega
  · rfl

/-- The example's cluster is connected. -/
theorem exF_conn : ∀ b ∈ exF, SameComp exF Const.a0 (0, 0, 0) b := by
  have step : ∀ a b : V3, a ∈ exF → b ∈ exF → dist3 a b ≤ 4 → AdjIn exF Const.a0 a b :=
    fun a b ha hb hd => ⟨ha, hb, hd⟩
  have h4 : SameComp exF Const.a0 (0, 0, 0) (4, 0, 0) :=
    .single (step _ _ (by decide) (by decide) (by decide))
  have h8 : SameComp exF Const.a0 (0, 0, 0) (8, 0, 0) :=
    h4.tail (step _ _ (by decide) (by decide) (by decide))
  have h12 : SameComp exF Const.a0 (0, 0, 0) (12, 0, 0) :=
    h8.tail (step _ _ (by decide) (by decide) (by decide))
  have h16 : SameComp exF Const.a0 (0, 0, 0) (16, 0, 0) :=
    h12.tail (step _ _ (by decide) (by decide) (by decide))
  have h20 : SameComp exF Const.a0 (0, 0, 0) (20, 0, 0) :=
    h16.tail (step _ _ (by decide) (by decide) (by decide))
  have h21 : SameComp exF Const.a0 (0, 0, 0) (21, 0, 0) :=
    h20.tail (step _ _ (by decide) (by decide) (by decide))
  intro b hb
  simp only [exF, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .refl
  · exact h4
  · exact h8
  · exact h12
  · exact h16
  · exact h20
  · exact h21

theorem exF_cluster (r : V3) (hr : r ∈ exL) : clusterOf exF r = exF := by
  ext b
  rw [mem_clusterOf]
  constructor
  · exact fun h => h.1
  · intro hb
    refine ⟨hb, ?_⟩
    have h0b := exF_conn b hb
    simp only [exL, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact h0b
    · exact (sameComp_symm exF _ (exF_conn _ (by decide))).trans h0b

theorem exL_cluster (r : V3) (hr : r ∈ exL) : clusterOf exL r = {r} := by
  ext b
  rw [mem_clusterOf, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    exact ex_trapped (by decide) hr h
  · rintro rfl
    exact ⟨hr, .refl⟩

theorem exPar_sumF : ∑ b ∈ exF, exPar b = 0 := by decide

theorem exPar_sumL : ∑ b ∈ exL, exPar b = 0 := by decide

theorem ex_hpar : ∀ b, exPar b ≠ 0 → b ∈ exL := by
  intro b hb
  unfold exPar at hb
  split_ifs at hb with h
  · simp only [exL, Finset.mem_insert, Finset.mem_singleton]
    exact h
  · exact absurd rfl hb

theorem ex_hP0 : ∀ r ∈ exL, InFamily3 exF exL (0, 0, 0) r → ∑ b ∈ clusterOf exL r, exPar b ≠ 0 := by
  intro r hr _
  rw [exL_cluster r hr, Finset.sum_singleton]
  simp only [exL, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl <;> decide

theorem ex_hP1 : ∀ r ∈ exL, InFamily3 exF exL (0, 0, 0) r → ∑ b ∈ clusterOf exF r, exPar b = 0 := by
  intro r hr _
  rw [exF_cluster r hr]
  exact exPar_sumF

theorem ex_hodd1 : ∑ b ∈ exL.filter (fun b => SameComp exL Const.a1 (0, 0, 0) b), exPar b ≠ 0 := by
  have h : exL.filter (fun b => SameComp exL Const.a1 (0, 0, 0) b) = {(0, 0, 0)} := by
    ext b
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      exact ex_trapped (by decide) (by decide) h
    · rintro rfl
      exact ⟨by decide, .refl⟩
  rw [h, Finset.sum_singleton]
  decide

theorem ex_hP2 :
    ∑ b ∈ exL.filter (fun b => ∃ k ∈ exL, SameComp exL Const.a1 (0, 0, 0) k ∧ SameComp exF Const.a0 k b),
      exPar b = 0 := by
  have h : exL.filter (fun b => ∃ k ∈ exL, SameComp exL Const.a1 (0, 0, 0) k ∧ SameComp exF Const.a0 k b) =
      exL := by
    ext b
    rw [Finset.mem_filter]
    constructor
    · exact fun h => h.1
    · intro hb
      exact ⟨hb, (0, 0, 0), by decide, .refl, exF_conn b (exL_sub hb)⟩
  rw [h]
  exact exPar_sumL

/-- **The hypotheses of `gen_skel3_parity_family` are satisfiable.** -/
theorem main_hyps_nonvac :
    ∃ (F Fl L : Finset V3) (par : V3 → ZMod 2) (e x : V3), L ⊆ Fl ∧ Fl ⊆ F ∧ (∀ b, par b ≠ 0 → b ∈ Fl) ∧
      e ∈ L ∧ x ∈ L ∧ InFamily3 F L e x ∧
      (∀ r ∈ L, InFamily3 F L e r → ∑ b ∈ clusterOf Fl r, par b ≠ 0) ∧
      (∀ r ∈ L, InFamily3 F L e r → ∑ b ∈ clusterOf F r, par b = 0) ∧
      ∑ b ∈ L.filter (fun b => SameComp L Const.a1 e b), par b ≠ 0 ∧
      ∑ b ∈ L.filter (fun b => ∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b), par b = 0 :=
  ⟨exF, exL, exL, exPar, (0, 0, 0), (0, 0, 0), Finset.Subset.refl _, exL_sub, ex_hpar, by decide, by decide, .refl,
    ex_hP0, ex_hP1, ex_hodd1, ex_hP2⟩

/-- **The main deterministic theorem is not vacuous**: on the example it produces a good skeleton rooted at the end
`e = 0`, with separated bad blocks and its route ending at the exit's cover. -/
theorem main_nonvac :
    ∃ k : Skel3, k.1 = (0, 0, 0) ∧ SkelOK k ∧
      dist3 (0, 0, 0) (endOf (0, 0, 0) (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks (0, 0, 0) k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks (0, 0, 0) k.2.2, b ∈ famF exF exL (0, 0, 0)) ∧
      (keyBlocks (0, 0, 0) k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length :=
  gen_skel3_parity_family exF exL exL (Finset.Subset.refl _) exL_sub exPar ex_hpar (by decide) (by decide) .refl
    ex_hP0 ex_hP1 ex_hodd1 ex_hP2

end QECD1
