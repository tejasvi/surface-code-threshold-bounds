import QECML.TwoD.Selection
import QECML.TwoD.Split

/-!
# T1 routes

A *route* is a start block `b₀` in the bottom strip and a list of moves: in-cluster steps (offset in
`S0 = {D ≤ |v|∞ ≤ A0}`), level-1 links (offset in `S1 = {D ≤ |v|∞ ≤ A1}`), and leaves (a block at offset in `S0` from
the current root; the route continues from the root). Grammar: a leaf only right after a link; after a leaf only a
link; a link followed by anything is followed by a leaf or a step (so every link unit except a final one has a leaf
or a nonempty run; the final unit is the entry into `G_top`). The counted blocks (all move blocks) lie strictly
between the strips, are pairwise at least `D` apart, and the route climbs to row `≥ n_y - 1 - h_s - A1`.

This is the class that the T1 generating function of the paper's proof counts: `(h_s + 1) n_x` starts,
`W1 = 1/(1 - U0)` for the initial run, `V1 = ε T1 (ε T0 + U0/(1 - U0))` per link unit, `1 + ε T1 W1` for the final unit.

* `routeSets`: the sets of counted blocks of valid routes (a finite set of block sets).
* `H2D_T1count`: the T1 counting bound, `∑_{B ∈ routeSets} ε^{|B|} ≤ C1 n_x e^{-s1 (n_y - H0)}`, a statement about
  block geometry only (it is implied by the sum over routes of the paper's proof, which counts each set at least once).
* `T1RouteExists`: every T1 event has a valid route whose counted blocks are all bad (the deterministic part).
* `h2dT1_of_routes` (proved): `T1RouteExists ∧ H2D_T1count ⟹ H2D_T1`, by the union bound and Hypothesis (H).
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable (G : S3Geom)

/-- A move of a route. -/
inductive Move where
  | step (b : G.Block)
  | link (b : G.Block)
  | leaf (b : G.Block)

variable {G}

/-- The block of a move. -/
def Move.blk : G.Move → G.Block
  | .step b => b
  | .link b => b
  | .leaf b => b

/-- The move is a link. -/
def Move.isLink : G.Move → Prop
  | .link _ => True
  | _ => False

/-- The move is a leaf. -/
def Move.isLeaf : G.Move → Prop
  | .leaf _ => True
  | _ => False

/-- The move is an in-cluster step. -/
def Move.isStep : G.Move → Prop
  | .step _ => True
  | _ => False

/-- The current block after the moves (a leaf does not move the route). -/
def endBlock : G.Block → List G.Move → G.Block
  | cur, [] => cur
  | _, .step b :: ms => endBlock b ms
  | _, .link b :: ms => endBlock b ms
  | cur, .leaf _ :: ms => endBlock cur ms

/-- The offsets of the moves: steps and leaves in `S0`, links in `S1`. -/
def MovesOK (D A0 A1 : ℕ) : G.Block → List G.Move → Prop
  | _, [] => True
  | cur, .step b :: ms => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0 ∧ MovesOK D A0 A1 b ms
  | cur, .link b :: ms => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1 ∧ MovesOK D A0 A1 b ms
  | cur, .leaf b :: ms => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0 ∧ MovesOK D A0 A1 cur ms

/-- The grammar of consecutive moves. -/
def GramOK (m m' : G.Move) : Prop :=
  (m'.isLeaf → m.isLink) ∧ (m.isLeaf → m'.isLink) ∧ (m.isLink → m'.isLeaf ∨ m'.isStep)

/-- A valid T1 route (separation `D`, link lengths `A0`, `A1`, strip height `hs`). -/
def ValidRoute (D A0 A1 hs : ℕ) (b0 : G.Block) (ms : List G.Move) : Prop :=
  b0.2.val ≤ hs ∧
  MovesOK D A0 A1 b0 ms ∧
  List.IsChain GramOK ms ∧
  (∀ m ∈ ms.head?, ¬ m.isLeaf) ∧
  (∀ m ∈ ms, hs + 1 ≤ m.blk.2.val ∧ m.blk.2.val + 2 + hs ≤ G.ny) ∧
  (ms.map Move.blk).Pairwise (fun b b' => D ≤ G.blockDist b b') ∧
  G.ny ≤ (endBlock b0 ms).2.val + 1 + hs + A1

variable (G)

/-- The sets of counted blocks of valid routes. -/
noncomputable def routeSets (D A0 A1 hs : ℕ) : Finset (Finset G.Block) :=
  Finset.univ.filter (fun B => ∃ b0 ms, ValidRoute D A0 A1 hs b0 ms ∧ B = (ms.map Move.blk).toFinset)

end S3Geom

/-- Union bound for a finite family of events. -/
theorem prob_exists_le {Ω ι : Type*} [Fintype Ω] {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (s : Finset ι)
    (A : ι → Ω → Prop) : prob P (fun ω => ∃ i ∈ s, A i ω) ≤ ∑ i ∈ s, prob P (A i) := by
  unfold prob
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hnn : ∀ i ∈ s, 0 ≤ (if A i ω then P ω else 0) := fun i _ => by
    split_ifs
    · exact hP ω
    · exact le_rfl
  split_ifs with h
  · obtain ⟨i, hi, hA⟩ := h
    have := Finset.single_le_sum hnn hi
    simpa [hA] using this
  · exact Finset.sum_nonneg hnn

theorem prob_mono {Ω : Type*} [Fintype Ω] {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) {A B : Ω → Prop}
    (h : ∀ ω, A ω → B ω) : prob P A ≤ prob P B := by
  unfold prob
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hA : A ω
  · simp [hA, h ω hA]
  · by_cases hB : B ω <;> simp [hA, hB, hP ω]

theorem pairwise_sym_mem {α : Type*} {R : α → α → Prop} (hR : ∀ x y, R x y → R y x) {l : List α}
    (h : l.Pairwise R) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) : R a b := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hne
    · exact h.1 b hb'
    · exact hR _ _ (h.1 a ha')
    · exact ih h.2 ha' hb'

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- The route existence statement on one code (deterministic). -/
def T1RouteExistsOn (a0 a1 : ℕ) : Prop :=
  ∀ E : G.Ed → ZMod 2, S.T1 a0 a1 E →
    ∃ (b0 : G.Block) (ms : List G.Move),
      G.ValidRoute G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) b0 ms ∧ ∀ m ∈ ms, S.bad E m.blk

end Stage1

namespace S3Geom

variable (G : S3Geom)

/-- The `ε`-weighted count of the counted-block sets of valid routes on one code. -/
noncomputable def routeCount (a0 a1 : ℕ) (ε : ℝ) : ℝ :=
  ∑ B ∈ G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1), ε ^ B.card

end S3Geom

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- On one code: routes and Hypothesis (H) bound `P(T1)` by the route count. -/
theorem prob_T1_le_routeCount (a0 a1 : ℕ) {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hex : S.T1RouteExistsOn a0 a1) (hH : S.HypH q ε) :
    prob (bernProd q) (fun E => S.T1 a0 a1 E) ≤ G.routeCount a0 a1 ε := by
  have hP := bernProd_nonneg (ι := G.Ed) hq0 hq1
  calc prob (bernProd q) (fun E => S.T1 a0 a1 E)
      ≤ prob (bernProd q) (fun E => ∃ B ∈ G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1),
          ∀ c ∈ B, S.bad E c) := by
        refine prob_mono hP fun E hT => ?_
        obtain ⟨b0, ms, hval, hbad⟩ := hex E hT
        refine ⟨(ms.map S3Geom.Move.blk).toFinset, ?_, fun c hc => ?_⟩
        · simp only [S3Geom.routeSets, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨b0, ms, hval, rfl⟩
        · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc)
          exact hbad m hm
    _ ≤ ∑ B ∈ G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1),
          prob (bernProd q) (fun E => ∀ c ∈ B, S.bad E c) := prob_exists_le hP _ _
    _ ≤ G.routeCount a0 a1 ε := by
        refine Finset.sum_le_sum fun B hB => hH B ?_ ?_
        · simp only [S3Geom.routeSets, Finset.mem_filter, Finset.mem_univ, true_and] at hB
          obtain ⟨b0, ms, hval, rfl⟩ := hB
          intro c hc
          obtain ⟨m, hm, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc)
          have hrow := hval.2.2.2.2.1 m hm
          have hhs : 1 ≤ hs a1 := by simp [hs]
          exact ⟨by omega, by omega⟩
        · simp only [S3Geom.routeSets, Finset.mem_filter, Finset.mem_univ, true_and] at hB
          obtain ⟨b0, ms, hval, rfl⟩ := hB
          intro c hc c' hc' hne
          exact pairwise_sym_mem (fun x y h => by rw [G.blockDist_comm]; exact h) hval.2.2.2.2.2.1
            (List.mem_toFinset.1 hc) (List.mem_toFinset.1 hc') hne

end Stage1

namespace S3Fam

variable (fam : S3Fam)

/-- **H2D_T1count** (the T1 counting bound; named hypothesis on block geometry only): on every code with
`n_x ≥ 5`, `n_y ≥ nyMin`, the `ε`-weighted number of counted-block sets of valid routes is at most
`C1 n_x e^{-s1 (n_y - H0)}`. -/
def H2D_T1count (a0 a1 : ℕ) (K : BoundConsts) (ε : ℝ) : Prop :=
  ∀ (nx ny : ℕ) (hnx : 5 ≤ nx) (hny : K.nyMin ≤ ny) (hny1 : 1 ≤ ny),
    (fam.geom nx ny (by omega) hny1).routeCount a0 a1 ε ≤ K.C1 * nx * Real.exp (-K.s1 * ((ny : ℝ) - K.H0))

/-- **T1RouteExists** (deterministic): on every code with `n_x ≥ 5`, `n_y ≥ nyMin`, every error in T1 has a valid
route whose counted blocks are all bad. -/
def T1RouteExists (a0 a1 : ℕ) (K : BoundConsts) : Prop :=
  ∀ (nx ny : ℕ) (hnx : 5 ≤ nx) (hny : K.nyMin ≤ ny) (hny1 : 1 ≤ ny),
    (fam.stage1 nx ny (by omega) hny1).T1RouteExistsOn a0 a1

/-- **The T1 term from routes**: `T1RouteExists ∧ H2D_T1count ⟹ H2D_T1`. -/
theorem h2dT1_of_routes (a0 a1 : ℕ) (K : BoundConsts) {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hex : fam.T1RouteExists a0 a1 K) (hcount : fam.H2D_T1count a0 a1 K ε) : fam.H2D_T1 a0 a1 K q ε :=
  fun nx ny hnx hny hny1 hH =>
    ((fam.stage1 nx ny (by omega) hny1).prob_T1_le_routeCount a0 a1 hq0 hq1 (hex nx ny hnx hny hny1) hH).trans
      (hcount nx ny hnx hny hny1)

/-- **Theorem B (a1 = 12 constants) with the T1 term from routes**: the T1 term is replaced by the deterministic
`T1RouteExists` and the counting bound `H2D_T1count`. -/
theorem theoremB_a12_routes (sp : S3Prog) (hV6 : sp.V6)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hex : (sp.toFam hV6).T1RouteExists 4 12 constsA12)
    (hcount : (sp.toFam hV6).H2D_T1count 4 12 constsA12 5e-4)
    (hT2 : (sp.toFam hV6).H2D_T2 4 12 Z constsA12 0.100 5e-4)
    (htype : (sp.toFam hV6).Htype 0.100) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        9.61e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.0351 * ((nyOf sp.L H : ℝ) - 31)) :=
  theoremB_a12_split sp hV6 Z
    ((sp.toFam hV6).h2dT1_of_routes 4 12 constsA12 (by norm_num) (by norm_num) hex hcount) hT2 htype hstat hq hW hH

end S3Fam

end QECML
