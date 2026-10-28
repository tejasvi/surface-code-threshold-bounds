import QECML.TwoD.T2Ends
import QECML.TwoD.T2Lam

/-!
# T2 skeletons and the T2 counting hypothesis

The T2 bound reduces, as the T1 bound does, to a deterministic existence statement and a pure counting hypothesis
on block geometry.

* `S3Geom.T2Sk`: a T2 skeleton: the bottom route (from a start block in the bottom strip, not counted), the
  intermediate families in order (each a cluster route with a witness), and the top route (from the landing root of
  the top family, stopped before the top strip). Validity `T2Sk.OK` collects the route rules, the witness span
  `Sw = a1 + 2 - D`, property (R) on the jumps between families, the exchange inequality (X) in block units (metric
  ratio `κ`, boundary constant `cH`), and the separation of the counted blocks.
* `S3Geom.t2Count`: the `ε`-weighted number of counted-block sets of valid skeletons;
  `S3Fam.H2D_T2count` bounds it by `C2 n_x e^{-s2 (n_y - H0)}`.
* `Stage1.prob_T2ev_le_t2Count` and `S3Fam.h2dT2ev_of_count`: skeleton existence and the counting bound give
  `H2D_T2ev`.
* `Stage1.t2SkelExistsOn` (proved): every T2 event without T1 has a valid skeleton whose counted blocks are bad, for a
  solver with weights in `[wmin, wmax]` on bulk edges and at most `wh` on half-edges (`κ = wmax / wmin`,
  `cH = 2 wh / (wmin L)`). Ingredients: `t2_stations` (the stations of the T2 path, the indexing of
  `metric_stations_block`), `fam_unit` (route and witness of an intermediate family), `bot_route` / `top_route` (the
  ends), `metric_stations_block` (the exchange inequality). `S3Fam.h2dT2ev_of_T2count`: `H2D_T2count ⟹ H2D_T2ev`.

Conventions of the class against the count of the paper's proof: a route cluster carries a leaf exactly when its
route part is empty; at an on-route witness cluster with an empty part the leaf is the first step of the witness
walk; an excursion leaves its cluster from the root (with the leaf) or from a walk starting at the leaf. If the
sub-path starts at `b₁`, the bottom route is the block of the check next to `b₁` (row 0, not counted); if it ends at
`b₂`, the top root is the block of the check next to `b₂` (top row, not counted, no top route). Otherwise the top
root, a level-1 block, is counted.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-- The block `ℓ1` distance. -/
def bl1 (b b' : G.Block) : ℕ := ndist b.1.val b'.1.val + ndist b.2.val b'.2.val

/-- The last block of `r :: a`. -/
def lastOf (r : G.Block) (a : List G.Block) : G.Block := ((r :: a).getLast?).getD r

/-- Consecutive blocks at offsets in `S0 = {D ≤ |v| ≤ A0}`. -/
def S0Chain (D A0 : ℕ) (l : List G.Block) : Prop :=
  List.IsChain (fun x y => D ≤ G.blockDist x y ∧ G.blockDist x y ≤ A0) l

variable (G)

/-- A cluster route: roots `r 0, …, r n` (the first root, then the targets of the links), route parts `a i` (the
selected blocks after the root, along the cluster's tree path), and leaves `lf i`. -/
structure CRoute where
  n : ℕ
  r : ℕ → G.Block
  a : ℕ → List G.Block
  lf : ℕ → Option G.Block

/-- The witness of a family route: (`on`) a walk `w` from the block `xb` of the route part (or the
leaf) of cluster `j`, ending at span at least `Sw` from the root of cluster `j`; (`off`) a walk `w` from `xb` in
cluster `jx`, a link to an excursion route `ex` through clusters off the route, whose last route part spans at least
`Sw` from its root. -/
inductive Wit where
  | on (j : ℕ) (xb : G.Block) (w : List G.Block)
  | off (jx : ℕ) (xb : G.Block) (w : List G.Block) (ex : CRoute G)

/-- A T2 skeleton: bottom route `b0, ms0` (`bf`: the sub-path starts at a family, not at `b₁`), the intermediate
families in order, top route `et, mst` (`tf`: the sub-path ends at a family, not at `b₂`). -/
structure T2Sk where
  b0 : G.Block
  ms0 : List G.Move
  bf : Bool
  fams : List (CRoute G × Wit G)
  et : G.Block
  mst : List G.Move
  tf : Bool

variable {G}

namespace CRoute

/-- **Validity of a cluster route**: steps in `S0` along each route part, a leaf (offset in `S0` from the root)
exactly at the clusters whose route part is empty, links in `S1` from the last block of each part to the next root. -/
def OK (D A0 A1 : ℕ) (cr : G.CRoute) : Prop :=
  (∀ i ≤ cr.n, S0Chain D A0 (cr.r i :: cr.a i)) ∧
  (∀ i ≤ cr.n, (cr.a i = [] ↔ (cr.lf i).isSome)) ∧
  (∀ i ≤ cr.n, ∀ l ∈ cr.lf i, D ≤ G.blockDist (cr.r i) l ∧ G.blockDist (cr.r i) l ≤ A0) ∧
  (∀ i < cr.n, D ≤ G.blockDist (lastOf (cr.r i) (cr.a i)) (cr.r (i + 1)) ∧
    G.blockDist (lastOf (cr.r i) (cr.a i)) (cr.r (i + 1)) ≤ A1)

/-- The exit block of a cluster route (the last block of its last route part). -/
def last (cr : G.CRoute) : G.Block := lastOf (cr.r cr.n) (cr.a cr.n)

/-- The counted blocks of a cluster route: roots, route parts, leaves. -/
def blocks (cr : G.CRoute) : List G.Block :=
  (List.range (cr.n + 1)).flatMap fun i => cr.r i :: (cr.a i ++ (cr.lf i).toList)

end CRoute

namespace Wit

/-- **Validity of a witness** of the cluster route `cr` (span `Sw`). The walk starts at the leaf of its cluster when
the route part there is empty (the leaf is the walk's first step), except for an excursion leaving from the root
itself. -/
def OK (D A0 A1 Sw : ℕ) (cr : G.CRoute) : G.Wit → Prop
  | .on j xb w => j ≤ cr.n ∧ (if cr.a j = [] then cr.lf j = some xb else xb ∈ cr.r j :: cr.a j) ∧
      S0Chain D A0 (xb :: w) ∧ Sw ≤ G.blockDist (cr.r j) (lastOf xb w)
  | .off jx xb w ex => jx ≤ cr.n ∧
      (if cr.a jx = [] then cr.lf jx = some xb ∨ (xb = cr.r jx ∧ w = []) else xb ∈ cr.r jx :: cr.a jx) ∧
      S0Chain D A0 (xb :: w) ∧ ex.OK D A0 A1 ∧
      D ≤ G.blockDist (lastOf xb w) (ex.r 0) ∧ G.blockDist (lastOf xb w) (ex.r 0) ≤ A1 ∧
      Sw ≤ G.blockDist (ex.r ex.n) ex.last

/-- The counted blocks of a witness. -/
def blocks : G.Wit → List G.Block
  | .on _ _ w => w
  | .off _ _ w ex => w ++ ex.blocks

end Wit

namespace T2Sk

/-- The covers `σ_0, …, σ_m`: the end of the bottom route, then the exits of the family routes. -/
def covers (sk : G.T2Sk) : List G.Block := endBlock sk.b0 sk.ms0 :: sk.fams.map (fun f => f.1.last)

/-- The landing roots `e_1, …, e_{m+1}`: the roots of the family routes, then the root of the top route. -/
def roots (sk : G.T2Sk) : List G.Block := sk.fams.map (fun f => f.1.r 0) ++ [sk.et]

/-- The jumps `(σ_i, e_{i+1})`, `i = 0, …, m`. -/
def jumps (sk : G.T2Sk) : List (G.Block × G.Block) := sk.covers.zip sk.roots

/-- The counted blocks: bottom route, family routes and witnesses, the top root if the sub-path ends at a family (a
level-1 block, counted with its `ε` as in the paper's proof), top route. -/
def counted (sk : G.T2Sk) : List G.Block :=
  sk.ms0.map Move.blk ++ (sk.fams.flatMap (fun f => f.1.blocks ++ f.2.blocks) ++
    ((if sk.tf then [sk.et] else []) ++ sk.mst.map Move.blk))

/-- **A valid T2 skeleton** (separation `D`, offsets `A0`, `A1`, strip height `hs`, witness span `Sw`, metric ratio
`κ`, boundary constant `cH`). -/
def OK (D A0 A1 hs Sw : ℕ) (κ cH : ℝ) (sk : G.T2Sk) : Prop :=
  -- the bottom route, its counted blocks strictly between the strips
  (sk.b0.2.val ≤ hs ∧ MovesOK D A0 A1 sk.b0 sk.ms0 ∧ List.IsChain GramOK sk.ms0 ∧
    (∀ m ∈ sk.ms0.head?, ¬ m.isLeaf) ∧ (∀ m ∈ sk.ms0.getLast?, ¬ m.isLink) ∧
    (∀ m ∈ sk.ms0, hs + 1 ≤ m.blk.2.val ∧ m.blk.2.val + 2 + hs ≤ G.ny) ∧
    (sk.bf = false → sk.ms0 = [] ∧ sk.b0.2.val = 0)) ∧
  -- the families, their blocks strictly between the strips
  (∀ f ∈ sk.fams, f.1.OK D A0 A1 ∧ f.2.OK D A0 A1 Sw f.1 ∧
    ∀ b ∈ f.1.blocks ++ f.2.blocks, hs + 1 ≤ b.2.val ∧ b.2.val + 2 + hs ≤ G.ny) ∧
  -- the top route, its blocks after the root strictly between the strips
  ((sk.tf = true → hs + 1 ≤ sk.et.2.val) ∧ MovesOK D A0 A1 sk.et sk.mst ∧ List.IsChain GramOK sk.mst ∧
    (∀ m ∈ sk.mst.head?, ¬ m.isLeaf) ∧ (∀ m ∈ sk.mst, hs + 1 ≤ m.blk.2.val ∧ m.blk.2.val + 2 + hs ≤ G.ny) ∧
    (G.ny ≤ sk.et.2.val + 1 + hs → sk.mst = []) ∧
    G.ny ≤ (endBlock sk.et sk.mst).2.val + 1 + hs + A1 ∧
    (sk.tf = false → sk.mst = [] ∧ sk.et.2.val + 1 = G.ny)) ∧
  -- property (R) on the jumps between two families (all jumps except a first one from `b₁` and a last one to
  -- `b₂`), and the exchange inequality (X) in block units
  (∀ i (hi : i < sk.jumps.length), (sk.bf = true ∨ i ≠ 0) → (sk.tf = true ∨ i + 1 ≠ sk.jumps.length) →
    Sw ≤ G.blockDist (sk.jumps[i]).1 (sk.jumps[i]).2) ∧
  (((sk.jumps.map fun q => bl1 q.1 q.2).sum : ℕ) : ℝ) ≤
    κ * (((sk.fams.map fun f => bl1 (f.1.r 0) f.1.last).sum : ℕ) : ℝ) + 2 * D * (sk.fams.length + 1) +
      2 * D * κ * sk.fams.length + κ * (((endBlock sk.b0 sk.ms0).2.val : ℝ) + D) +
      κ * ((G.ny : ℝ) - sk.et.2.val) + cH ∧
  -- the counted blocks: in the sampled rows, pairwise at least `D` apart
  (∀ b ∈ sk.counted, 2 ≤ b.2.val ∧ b.2.val + 3 ≤ G.ny) ∧
  sk.counted.Pairwise (fun b b' => D ≤ G.blockDist b b')

end T2Sk

variable (G)

/-- The counted-block sets of valid T2 skeletons. -/
noncomputable def t2SkelSets (D A0 A1 hs Sw : ℕ) (κ cH : ℝ) : Finset (Finset G.Block) :=
  Finset.univ.filter (fun B => ∃ sk : G.T2Sk, sk.OK D A0 A1 hs Sw κ cH ∧ B = sk.counted.toFinset)

/-- The `ε`-weighted count of the counted-block sets of valid T2 skeletons on one code. -/
noncomputable def t2Count (a0 a1 : ℕ) (κ cH ε : ℝ) : ℝ :=
  ∑ B ∈ G.t2SkelSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1) (a1 + 2 - G.D) κ cH, ε ^ B.card

end S3Geom

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- **T2 skeleton existence** on one code (deterministic): every error in the T2 event without T1 has a valid
skeleton whose counted blocks are all bad. -/
def T2SkelExistsOn (a0 a1 : ℕ) (Z : Solver G) (κ cH : ℝ) : Prop :=
  ∀ E : G.Ed → ZMod 2, S.T2ev a0 a1 Z E → ¬ S.T1 a0 a1 E →
    ∃ sk : G.T2Sk, sk.OK G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (a1 + 2 - G.D) κ cH ∧
      ∀ c ∈ sk.counted, S.bad E c

/-- On one code: skeletons and Hypothesis (H) bound `P(T2ev ∧ ¬T1)` by the skeleton count. -/
theorem prob_T2ev_le_t2Count (a0 a1 : ℕ) (Z : Solver G) (κ cH : ℝ) {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hex : S.T2SkelExistsOn a0 a1 Z κ cH) (hH : S.HypH q ε) :
    prob (bernProd q) (fun E => S.T2ev a0 a1 Z E ∧ ¬ S.T1 a0 a1 E) ≤ G.t2Count a0 a1 κ cH ε := by
  have hP := bernProd_nonneg (ι := G.Ed) hq0 hq1
  calc prob (bernProd q) (fun E => S.T2ev a0 a1 Z E ∧ ¬ S.T1 a0 a1 E)
      ≤ prob (bernProd q) (fun E => ∃ B ∈ G.t2SkelSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1)
          (a1 + 2 - G.D) κ cH, ∀ c ∈ B, S.bad E c) := by
        refine prob_mono hP fun E hT => ?_
        obtain ⟨sk, hok, hbad⟩ := hex E hT.1 hT.2
        refine ⟨sk.counted.toFinset, ?_, fun c hc => hbad c (List.mem_toFinset.1 hc)⟩
        simp only [S3Geom.t2SkelSets, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨sk, hok, rfl⟩
    _ ≤ ∑ B ∈ G.t2SkelSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (a1 + 2 - G.D) κ cH,
          prob (bernProd q) (fun E => ∀ c ∈ B, S.bad E c) := prob_exists_le hP _ _
    _ ≤ G.t2Count a0 a1 κ cH ε := by
        refine Finset.sum_le_sum fun B hB => hH B ?_ ?_
        · simp only [S3Geom.t2SkelSets, Finset.mem_filter, Finset.mem_univ, true_and] at hB
          obtain ⟨sk, hok, rfl⟩ := hB
          intro c hc
          exact hok.2.2.2.2.2.1 c (List.mem_toFinset.1 hc)
        · simp only [S3Geom.t2SkelSets, Finset.mem_filter, Finset.mem_univ, true_and] at hB
          obtain ⟨sk, hok, rfl⟩ := hB
          intro c hc c' hc' hne
          exact pairwise_sym_mem (fun x y h => by rw [G.blockDist_comm]; exact h) hok.2.2.2.2.2.2
            (List.mem_toFinset.1 hc) (List.mem_toFinset.1 hc') hne

end Stage1

namespace S3Fam

variable (fam : S3Fam)

/-- **H2D_T2count** (the T2 counting bound; named hypothesis on block geometry only): on every code with
`n_x ≥ 5`, `n_y ≥ nyMin`, the `ε`-weighted number of counted-block sets of valid T2 skeletons (metric ratio `κ`,
boundary constant `cH`) is at most `C2 n_x e^{-s2 (n_y - H0)}`. -/
def H2D_T2count (a0 a1 : ℕ) (κ cH : ℝ) (K : BoundConsts) (ε : ℝ) : Prop :=
  ∀ (nx ny : ℕ) (hnx : 5 ≤ nx) (hny : K.nyMin ≤ ny) (hny1 : 1 ≤ ny),
    (fam.geom nx ny (by omega) hny1).t2Count a0 a1 κ cH ε ≤ K.C2 * nx * Real.exp (-K.s2 * ((ny : ℝ) - K.H0))

/-- **T2SkelExists** (deterministic): on every code with `n_x ≥ 5`, `n_y ≥ nyMin`, every error in the T2 event
without T1 has a valid skeleton whose counted blocks are all bad. -/
def T2SkelExists (a0 a1 : ℕ) (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny))
    (κ cH : ℝ) (K : BoundConsts) : Prop :=
  ∀ (nx ny : ℕ) (hnx : 5 ≤ nx) (hny : K.nyMin ≤ ny) (hny1 : 1 ≤ ny),
    (fam.stage1 nx ny (by omega) hny1).T2SkelExistsOn a0 a1 (Z nx ny (by omega) hny1) κ cH

/-- **The T2 term from skeletons**: `T2SkelExists ∧ H2D_T2count ⟹ H2D_T2ev`. -/
theorem h2dT2ev_of_count (a0 a1 : ℕ)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny)) (κ cH : ℝ)
    (K : BoundConsts) {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hex : fam.T2SkelExists a0 a1 Z κ cH K)
    (hcount : fam.H2D_T2count a0 a1 κ cH K ε) : fam.H2D_T2ev a0 a1 Z K q ε :=
  fun nx ny hnx hny hny1 hH =>
    ((fam.stage1 nx ny (by omega) hny1).prob_T2ev_le_t2Count a0 a1 _ κ cH hq0 hq1 (hex nx ny hnx hny hny1)
      hH).trans (hcount nx ny hnx hny hny1)

end S3Fam

/-! ### Existence: the route and witness of an intermediate family -/

namespace S3Geom

variable {G : S3Geom}

theorem lastOf_eq {r s : G.Block} {a : List G.Block} (h : (r :: a).getLast? = some s) : lastOf r a = s := by
  simp [lastOf, h]

/-- The cluster route with roots `r i`, parts `a i`, and the leaf `lv i` at the clusters whose part is empty. -/
def CRoute.ofParts (n : ℕ) (r : ℕ → G.Block) (a : ℕ → List G.Block) (lv : ℕ → G.Block) : G.CRoute :=
  ⟨n, r, a, fun i => if a i = [] then some (lv i) else none⟩

end S3Geom

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- A selected walk from a route node, avoiding the route part, without repeated blocks (`sel_branch` with the
walk's blocks distinct). -/
theorem sel_branch_nd {a0 : ℕ} {Sel : Finset G.Block} {r b' : G.Block} {route : List G.Block}
    (hsep : ∀ b ∈ Sel, ∀ b' ∈ Sel, b ≠ b' → G.D ≤ G.blockDist b b')
    (hconn : ∀ b ∈ Sel, Relation.ReflTransGen
      (fun y z => y ∈ Sel ∧ z ∈ Sel ∧ G.blockDist y z ≤ G.D - 1 + a0) r b)
    (hrS : r ∈ Sel) (hb'S : b' ∈ Sel) (hr : r ∈ route) :
    ∃ xb w, xb ∈ route ∧ (∀ b ∈ w, b ∈ Sel ∧ b ∉ route) ∧ (xb :: w).Nodup ∧
      S3Geom.S0Chain G.D (G.D - 1 + a0) (xb :: w) ∧ S3Geom.lastOf xb w = b' := by
  obtain ⟨q, hqh, hql, hqnd, hqS, hqch⟩ := S3Geom.exists_simple_path hrS (hconn b' hb'S)
  obtain ⟨pre, xb, w, hsplit, hx, hw⟩ := branch_split route q hr hqh
  subst hsplit
  have hmemq : ∀ b ∈ xb :: w, b ∈ pre ++ xb :: w := fun b hb => List.mem_append_right pre hb
  refine ⟨xb, w, hx, fun b hb => ⟨hqS b (hmemq b (List.mem_cons_of_mem _ hb)), hw b hb⟩,
    hqnd.sublist (List.sublist_append_right pre _),
    hqch.right_of_append.imp_of_mem_imp fun y z hy hz hyz =>
      ⟨hsep y (hqS y (hmemq y hy)) z (hqS z (hmemq z hz)) hyz.1, hyz.2⟩, ?_⟩
  rw [S3Geom.getLast?_append_cons] at hql
  exact S3Geom.lastOf_eq hql

/-- **A leaf from (W0)**: the root of an interior cluster, a level-1 block, has a second selected block within
`A0`. -/
theorem sel_leaf {a0 : ℕ} (ha0 : 2 ≤ a0) (hDa : G.D ≤ a0 + 1) {E : G.Ed → ZMod 2} {r : G.Block}
    (hr : r ∈ S.lev1 a0 E) (hint : Interior (S.cluster E a0 r)) {Sel : Finset G.Block}
    (hconn : ∀ b ∈ Sel, Relation.ReflTransGen
      (fun y z => y ∈ Sel ∧ z ∈ Sel ∧ G.blockDist y z ≤ G.D - 1 + a0) r b)
    (hcov : ∀ c ∈ S.cluster E a0 r, ∃ b ∈ Sel, G.blockDist c b ≤ G.D - 1) (hrS : r ∈ Sel) :
    ∃ l ∈ Sel, l ≠ r ∧ G.blockDist r l ≤ G.D - 1 + a0 := by
  obtain ⟨hfl, hunres⟩ := hr
  have hodd : ∑ v, G.restrictTo (G.comp (S3Geom.flaggedSet (S.resid E)) a0 r) (S.resid E) v ≠ 0 :=
    fun h => hunres (Or.inl h)
  obtain ⟨c'', hc''K, -, hfar⟩ := S.W0 ha0 hfl hint hodd
  have hfar' := hfar r (S3Geom.mem_comp_self hfl)
  obtain ⟨s, hsS, hcs⟩ := hcov c'' hc''K
  have hsne : s ≠ r := by
    rintro rfl
    rw [G.blockDist_comm] at hcs
    omega
  obtain ⟨l, hhead, hlast, -, hmemL, hch⟩ := S3Geom.exists_simple_path hrS (hconn s hsS)
  rcases l with _ | ⟨e', _ | ⟨y, l⟩⟩
  · simp at hhead
  · simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    exact absurd (hlast.symm.trans hhead) hsne
  · simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    rw [List.isChain_cons_cons] at hch
    exact ⟨y, hmemL y (by simp), fun h => hch.1.1 h.symm, hch.1.2⟩

/-- **The cluster route of a chain**: roots `(f i).1`, route parts `rest i`, leaves `lv i` at the clusters with an
empty part. It is valid, ends at the cover `sEnd n` of the last exit, and its blocks lie in the selections and are
pairwise at least `D` apart. -/
theorem cr_of_chain {a0 a1 : ℕ} (hDa : G.D ≤ a0 + 1) {E : G.Ed → ZMod 2} {n : ℕ} {f : ℕ → G.Block × G.Block}
    (hL : ∀ i < n, S.LinkOK a0 a1 E (f i).2 (f (i + 1)).1)
    (hdist : ∀ i j, i < j → j ≤ n → S.cluster E a0 (f i).1 ≠ S.cluster E a0 (f j).1)
    {Sel : ℕ → Finset G.Block} {rest : ℕ → List G.Block} {sEnd : ℕ → G.Block}
    (hdat : ∀ i ≤ n, (∀ b ∈ Sel i, b ∈ S.cluster E a0 (f i).1) ∧
        (∀ b ∈ Sel i, ∀ b' ∈ Sel i, b ≠ b' → G.D ≤ G.blockDist b b') ∧
        ((f i).1 :: rest i).Nodup ∧ (∀ b ∈ (f i).1 :: rest i, b ∈ Sel i) ∧
        List.IsChain (fun y z => y ≠ z ∧ G.blockDist y z ≤ G.D - 1 + a0) ((f i).1 :: rest i) ∧
        ((f i).1 :: rest i).getLast? = some (sEnd i) ∧ G.blockDist (f i).2 (sEnd i) ≤ G.D - 1)
    {lv : ℕ → G.Block} (hlv : ∀ i ≤ n, rest i = [] → lv i ∈ Sel i ∧ lv i ≠ (f i).1 ∧
        G.blockDist (f i).1 (lv i) ≤ G.D - 1 + a0) :
    (S3Geom.CRoute.ofParts n (fun i => (f i).1) rest lv).OK G.D (G.D - 1 + a0) (G.D - 1 + a1) ∧
      (S3Geom.CRoute.ofParts n (fun i => (f i).1) rest lv).last = sEnd n ∧
      (∀ b ∈ (S3Geom.CRoute.ofParts n (fun i => (f i).1) rest lv).blocks, ∃ i ≤ n, b ∈ Sel i) ∧
      (S3Geom.CRoute.ofParts n (fun i => (f i).1) rest lv).blocks.Pairwise
        (fun b b' => G.D ≤ G.blockDist b b') := by
  -- the blocks of cluster `i`
  have hcl : ∀ i ≤ n, (∀ b ∈ (f i).1 :: (rest i ++ (if rest i = [] then some (lv i) else none).toList),
      b ∈ Sel i) ∧ ((f i).1 :: (rest i ++ (if rest i = [] then some (lv i) else none).toList)).Nodup := by
    intro i hi
    obtain ⟨-, -, hnd, hmem, -, -, -⟩ := hdat i hi
    by_cases hr : rest i = []
    · obtain ⟨hlS, hlne, -⟩ := hlv i hi hr
      have hr0 := hmem (f i).1 List.mem_cons_self
      simp only [hr, ↓reduceIte, Option.toList_some, List.nil_append]
      refine ⟨fun b hb => ?_, ?_⟩
      · rcases List.mem_pair.1 hb with rfl | rfl
        · exact hr0
        · exact hlS
      · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
          List.nodup_nil, and_true]
        exact fun h => hlne h.symm
    · simp only [hr, ↓reduceIte, Option.toList_none, List.append_nil]
      exact ⟨hmem, hnd⟩
  have hsepK : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → ∀ x ∈ Sel i, ∀ y ∈ Sel j, G.D ≤ G.blockDist x y := by
    intro i hi j hj hij x hx y hy
    have hxK := (hdat i hi).1 x hx
    have hyK := (hdat j hj).1 y hy
    rcases lt_or_gt_of_ne hij with h | h
    · have := S.cluster_sep hxK hyK (hdist i j h hj)
      omega
    · have := S.cluster_sep hyK hxK (hdist j i h hi)
      rw [G.blockDist_comm] at this
      omega
  have hlast : ∀ i ≤ n, S3Geom.lastOf (f i).1 (rest i) = sEnd i := fun i hi =>
    S3Geom.lastOf_eq (hdat i hi).2.2.2.2.2.1
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun i hi l hl => ?_, fun i hi => ?_⟩, hlast n le_rfl, fun b hb => ?_, ?_⟩
  · -- steps in `S0`
    obtain ⟨-, hsep, -, hmem, hch, -, -⟩ := hdat i hi
    exact hch.imp_of_mem_imp fun y z hy hz hyz => ⟨hsep y (hmem y hy) z (hmem z hz) hyz.1, hyz.2⟩
  · -- a leaf exactly at the empty parts
    show rest i = [] ↔ (if rest i = [] then some (lv i) else none).isSome
    by_cases hr : rest i = [] <;> simp [hr]
  · -- the leaf offset
    have hl' : (if rest i = [] then some (lv i) else none) = some l := hl
    by_cases hr : rest i = []
    · rw [ite_eq_left hr, Option.some.injEq] at hl'
      subst hl'
      obtain ⟨hlS, hlne, hll⟩ := hlv i hi hr
      obtain ⟨-, hsep, -, hmem, -, -, -⟩ := hdat i hi
      exact ⟨hsep _ (hmem _ List.mem_cons_self) _ hlS hlne.symm, hll⟩
    · rw [ite_eq_right hr] at hl'
      exact absurd hl' (by simp)
  · -- links from the cover of an exit to the next root
    show G.D ≤ G.blockDist (S3Geom.lastOf (f i).1 (rest i)) (f (i + 1)).1 ∧
      G.blockDist (S3Geom.lastOf (f i).1 (rest i)) (f (i + 1)).1 ≤ G.D - 1 + a1
    rw [hlast i hi.le]
    obtain ⟨-, -, -, hmem, -, hlastP, hxs⟩ := hdat i hi.le
    obtain ⟨-, -, -, hmem', -, -, -⟩ := hdat (i + 1) hi
    refine ⟨hsepK i hi.le (i + 1) hi (by omega) _ (hmem _ (List.mem_of_getLast? hlastP)) _
      (hmem' _ List.mem_cons_self), ?_⟩
    have t1 := G.blockDist_triangle (sEnd i) (f i).2 (f (i + 1)).1
    have t2 : G.blockDist (sEnd i) (f i).2 ≤ G.D - 1 := by
      rw [G.blockDist_comm]
      exact hxs
    have t3 := (hL i hi).2.2
    omega
  · -- the blocks lie in the selections
    obtain ⟨i, hi, hb⟩ := List.mem_flatMap.1 hb
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (List.mem_range.1 hi)
    exact ⟨i, hi', (hcl i hi').1 b hb⟩
  · -- separation
    refine List.pairwise_flatMap.2 ⟨fun i hi => ?_, ?_⟩
    · have hi' : i ≤ n := Nat.lt_succ_iff.1 (List.mem_range.1 hi)
      obtain ⟨hmem, hnd⟩ := hcl i hi'
      obtain ⟨-, hsep, -, -, -, -, -⟩ := hdat i hi'
      exact List.Pairwise.imp_of_mem (fun hx hy hxy => hsep _ (hmem _ hx) _ (hmem _ hy) hxy) hnd
    · refine List.pairwise_lt_range.imp_of_mem fun hi hj hij x hx y hy => ?_
      have hi' : _ ≤ n := Nat.lt_succ_iff.1 (List.mem_range.1 hi)
      have hj' : _ ≤ n := Nat.lt_succ_iff.1 (List.mem_range.1 hj)
      exact hsepK _ hi' _ hj' (by omega) x ((hcl _ hi').1 x hx) y ((hcl _ hj').1 y hy)

theorem lastOf_cons (r a : G.Block) (l : List G.Block) : S3Geom.lastOf r (a :: l) = S3Geom.lastOf a l := by
  simp [S3Geom.lastOf, List.getLast?_cons]

/-- Blocks of distinct clusters are at least `D` apart. -/
theorem sep_of_cluster_ne {a0 : ℕ} (hDa : G.D ≤ a0 + 1) {E : G.Ed → ZMod 2} {c c' x y : G.Block}
    (hx : x ∈ S.cluster E a0 c) (hy : y ∈ S.cluster E a0 c') (hne : S.cluster E a0 c ≠ S.cluster E a0 c') :
    G.D ≤ G.blockDist x y := by
  have := S.cluster_sep hx hy hne
  omega

/-- **The skeleton unit of an intermediate family**: a valid cluster route from the entry `e`
to a selected block within `D - 1` of the exit `x`, with a valid witness; all its blocks lie in the family and are
pairwise at least `D` apart. -/
theorem fam_unit {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (hD1 : 1 ≤ G.D) (hDa : G.D ≤ a0 + 1) (Z : Solver G)
    {E : G.Ed → ZMod 2} {e x : G.Block} (he : e ∈ S.lev1 a0 E)
    (hodd : ¬ G.resolved (S.resid E) ((a1 + 1) / 2) (S.lev1comp a0 a1 E e))
    (hx : x ∈ S.family a0 a1 E e) (hx1 : x ∈ S.lev1 a0 E)
    (hint : ∀ c ∈ S.family a0 a1 E e, hs a1 < c.2.val ∧ c.2.val + 1 + hs a1 < G.ny) :
    ∃ (cr : G.CRoute) (wt : G.Wit), cr.OK G.D (G.D - 1 + a0) (G.D - 1 + a1) ∧
      wt.OK G.D (G.D - 1 + a0) (G.D - 1 + a1) (a1 + 2 - G.D) cr ∧ cr.r 0 = e ∧
      G.blockDist x cr.last ≤ G.D - 1 ∧ (∀ b ∈ cr.blocks ++ wt.blocks, b ∈ S.family a0 a1 E e) ∧
      (cr.blocks ++ wt.blocks).Pairwise (fun b b' => G.D ≤ G.blockDist b b') := by
  have hebad : S.badD E e := S.badD_of_lev1 he
  obtain ⟨n, f, Sel, rest, sEnd, -, hfch, hdist, hdat, -⟩ := S.fam_route ha0 hD1 hDa he hx hint
  have hfam := S.fchain_family hebad hfch
  obtain ⟨hP, hL, h0, hn⟩ := hfch
  have hdat7 : ∀ i ≤ n, (∀ b ∈ Sel i, b ∈ S.cluster E a0 (f i).1) ∧
      (∀ b ∈ Sel i, ∀ b' ∈ Sel i, b ≠ b' → G.D ≤ G.blockDist b b') ∧
      ((f i).1 :: rest i).Nodup ∧ (∀ b ∈ (f i).1 :: rest i, b ∈ Sel i) ∧
      List.IsChain (fun y z => y ≠ z ∧ G.blockDist y z ≤ G.D - 1 + a0) ((f i).1 :: rest i) ∧
      ((f i).1 :: rest i).getLast? = some (sEnd i) ∧ G.blockDist (f i).2 (sEnd i) ≤ G.D - 1 := by
    intro i hi
    obtain ⟨h1, h2, -, -, h5, h6, h7, h8, h9⟩ := hdat i hi
    exact ⟨h1, h2, h5, h6, h7, h8, h9⟩
  have hroot1 : ∀ i ≤ n, (f i).1 ∈ S.lev1 a0 E := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, h0]
      exact he
    · have := (hL (i - 1) (by omega)).2.1
      rwa [show i - 1 + 1 = i by omega] at this
  have hhs1 : 1 ≤ hs a1 := by simp [hs]
  have hintF : ∀ k, (∀ c ∈ S.cluster E a0 k, c ∈ S.family a0 a1 E e) → Interior (S.cluster E a0 k) := by
    intro k hk c hc hdecl
    have := hint c (hk c hc)
    rcases hdecl with h | h <;> omega
  -- (W0) leaves at every route cluster
  have hleafE : ∀ i, ∃ l : G.Block, i ≤ n → l ∈ Sel i ∧ l ≠ (f i).1 ∧ G.blockDist (f i).1 l ≤ G.D - 1 + a0 := by
    intro i
    by_cases hi : i ≤ n
    · obtain ⟨-, -, hconn, hcov, -, hmem, -, -, -⟩ := hdat i hi
      obtain ⟨l, hlS, hl⟩ := S.sel_leaf ha0 hDa (hroot1 i hi) (hintF _ (hfam i hi)) hconn hcov
        (hmem _ List.mem_cons_self)
      exact ⟨l, fun _ => ⟨hlS, hl⟩⟩
    · exact ⟨e, fun h => absurd h hi⟩
  choose leaf hleaf using hleafE
  -- the blocks of route cluster `i`
  have hclS : ∀ (lv : ℕ → G.Block), (∀ i ≤ n, rest i = [] → lv i ∈ Sel i ∧ lv i ≠ (f i).1 ∧
      G.blockDist (f i).1 (lv i) ≤ G.D - 1 + a0) → ∀ i ≤ n,
      ∀ b ∈ (f i).1 :: (rest i ++ (if rest i = [] then some (lv i) else none).toList), b ∈ Sel i := by
    intro lv hlv i hi b hb
    obtain ⟨-, -, -, hmem, -, -, -⟩ := hdat7 i hi
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hmem _ List.mem_cons_self
    rcases List.mem_append.1 hb with hb | hb
    · exact hmem _ (List.mem_cons_of_mem _ hb)
    · by_cases hr : rest i = []
      · simp only [hr, ↓reduceIte, Option.toList_some, List.mem_singleton] at hb
        subst hb
        exact (hlv i hi hr).1
      · simp [hr] at hb
  have hmemB : ∀ (lv : ℕ → G.Block) b, b ∈ (S3Geom.CRoute.ofParts n (fun i => (f i).1) rest lv).blocks →
      ∃ i ≤ n, b ∈ (f i).1 :: (rest i ++ (if rest i = [] then some (lv i) else none).toList) := by
    intro lv b hb
    obtain ⟨i, hi, hb⟩ := List.mem_flatMap.1 hb
    exact ⟨i, Nat.lt_succ_iff.1 (List.mem_range.1 hi), hb⟩
  -- separation of route blocks from a walk in the selection of route cluster `j`
  have hsepW : ∀ (lv : ℕ → G.Block), (∀ i ≤ n, rest i = [] → lv i ∈ Sel i ∧ lv i ≠ (f i).1 ∧
      G.blockDist (f i).1 (lv i) ≤ G.D - 1 + a0) → ∀ j ≤ n, ∀ y ∈ Sel j,
      y ∉ (f j).1 :: (rest j ++ (if rest j = [] then some (lv j) else none).toList) →
      ∀ b ∈ (S3Geom.CRoute.ofParts n (fun i => (f i).1) rest lv).blocks, G.D ≤ G.blockDist b y := by
    intro lv hlv j hj y hy hyout b hb
    obtain ⟨i, hi, hbi⟩ := hmemB lv b hb
    have hbS := hclS lv hlv i hi b hbi
    rcases eq_or_ne i j with rfl | hij
    · exact (hdat7 i hi).2.1 b hbS y hy (fun h => hyout (h ▸ hbi))
    · rcases lt_or_gt_of_ne hij with h | h
      · exact S.sep_of_cluster_ne hDa ((hdat7 i hi).1 b hbS) ((hdat7 j hj).1 y hy) (hdist i j h hj)
      · have := S.sep_of_cluster_ne hDa ((hdat7 j hj).1 y hy) ((hdat7 i hi).1 b hbS) (hdist j i h hi)
        rwa [G.blockDist_comm] at this
  -- route blocks lie in the family
  have hfamB : ∀ (lv : ℕ → G.Block), (∀ i ≤ n, rest i = [] → lv i ∈ Sel i ∧ lv i ≠ (f i).1 ∧
      G.blockDist (f i).1 (lv i) ≤ G.D - 1 + a0) →
      ∀ b ∈ (S3Geom.CRoute.ofParts n (fun i => (f i).1) rest lv).blocks, b ∈ S.family a0 a1 E e := by
    intro lv hlv b hb
    obtain ⟨i, hi, hbi⟩ := hmemB lv b hb
    exact hfam i hi b ((hdat7 i hi).1 b (hclS lv hlv i hi b hbi))
  have hfch : S.FChain a0 a1 E e x n f := ⟨hP, hL, h0, hn⟩
  have hcov : ∀ j ≤ n, ∀ c ∈ S.cluster E a0 (f j).1, ∃ b ∈ Sel j, G.blockDist c b ≤ G.D - 1 :=
    fun j hj => (hdat j hj).2.2.2.1
  have hsEnd : ∀ j ≤ n, sEnd j ∈ Sel j ∧ G.blockDist (f j).2 (sEnd j) ≤ G.D - 1 := fun j hj =>
    ⟨(hdat j hj).2.2.2.2.2.1 _ (List.mem_of_getLast? (hdat j hj).2.2.2.2.2.2.2.1), (hdat j hj).2.2.2.2.2.2.2.2⟩
  have hxlast : ∀ lv : ℕ → G.Block, G.blockDist x (S3Geom.CRoute.ofParts n (fun i => (f i).1) rest lv).last ≤
      G.D - 1 := by
    intro lv
    show G.blockDist x (S3Geom.lastOf (f n).1 (rest n)) ≤ G.D - 1
    rw [S3Geom.lastOf_eq (hdat7 n le_rfl).2.2.2.2.2.1, ← hn]
    exact (hdat7 n le_rfl).2.2.2.2.2.2
  -- the walk of a witness: a leaf choice `lv`, a start `xb'` and a walk `w'` in the selection of cluster `j`
  have hwalk : ∀ j ≤ n, ∀ xb w, xb ∈ (f j).1 :: rest j → (∀ b ∈ w, b ∈ Sel j ∧ b ∉ (f j).1 :: rest j) →
      (xb :: w).Nodup → S3Geom.S0Chain G.D (G.D - 1 + a0) (xb :: w) →
      ∃ (lv : ℕ → G.Block) (xb' : G.Block) (w' : List G.Block),
        (∀ i ≤ n, rest i = [] → lv i ∈ Sel i ∧ lv i ≠ (f i).1 ∧ G.blockDist (f i).1 (lv i) ≤ G.D - 1 + a0) ∧
        (if rest j = [] then (if rest j = [] then some (lv j) else none) = some xb' ∨ (xb' = (f j).1 ∧ w' = [])
          else xb' ∈ (f j).1 :: rest j) ∧
        S3Geom.S0Chain G.D (G.D - 1 + a0) (xb' :: w') ∧ S3Geom.lastOf xb' w' = S3Geom.lastOf xb w ∧
        (∀ b ∈ w', b ∈ Sel j) ∧ w'.Nodup ∧
        (∀ b ∈ w', b ∉ (f j).1 :: (rest j ++ (if rest j = [] then some (lv j) else none).toList)) := by
    intro j hj xb w hxb hw hnd hch
    by_cases hrj : rest j = []
    · have hxbj : xb = (f j).1 := by simpa [hrj] using hxb
      subst hxbj
      rcases w with _ | ⟨w1, w'⟩
      · -- the walk is empty
        refine ⟨leaf, (f j).1, [], fun i hi _ => hleaf i hi, ?_, hch, rfl, fun b hb => absurd hb (by simp),
          List.nodup_nil, fun b hb => absurd hb (by simp)⟩
        rw [ite_eq_left hrj]
        exact Or.inr ⟨rfl, rfl⟩
      · -- the first block of the walk replaces the leaf
        have hw1 := hw w1 List.mem_cons_self
        have hch2 := List.isChain_cons_cons.1 (show List.IsChain
          (fun x y => G.D ≤ G.blockDist x y ∧ G.blockDist x y ≤ G.D - 1 + a0) ((f j).1 :: w1 :: w') from hch)
        have hw1ne : w1 ≠ (f j).1 := fun h => hw1.2 (by rw [h]; exact List.mem_cons_self)
        have hnd' := List.nodup_cons.1 (List.nodup_cons.1 hnd).2
        refine ⟨fun i => if i = j then w1 else leaf i, w1, w', fun i hi hri => ?_, ?_, hch2.2, ?_,
          fun b hb => (hw b (List.mem_cons_of_mem _ hb)).1, hnd'.2, fun b hb hbin => ?_⟩
        · by_cases hij : i = j
          · subst hij
            simp only [↓reduceIte]
            exact ⟨hw1.1, hw1ne, hch2.1.2⟩
          · simp only [hij, ↓reduceIte]
            exact hleaf i hi
        · rw [ite_eq_left hrj, ite_eq_left hrj]
          left
          simp
        · rw [lastOf_cons]
        · simp only [hrj, eq_self, ↓reduceIte, Option.toList_some, List.nil_append, List.mem_cons,
            List.not_mem_nil, or_false] at hbin
          rcases hbin with h | h
          · exact (hw b (List.mem_cons_of_mem _ hb)).2 (by rw [h]; exact List.mem_cons_self)
          · exact hnd'.1 (by rw [← h]; exact hb)
    · refine ⟨leaf, xb, w, fun i hi _ => hleaf i hi, ?_, hch, rfl,
        fun b hb => (hw b hb).1, (List.nodup_cons.1 hnd).2, fun b hb hbin => ?_⟩
      · rw [ite_eq_right hrj]
        exact hxb
      · simp only [hrj, ↓reduceIte, Option.toList_none, List.append_nil] at hbin
        exact (hw b hb).2 hbin
  rcases S.fam_witness ha0 hD1 Z he hodd hx1 hint hfch hcov hsEnd with ⟨j, hj, b', hb', hfar⟩ |
    ⟨hmemK, c'', hc''1, hoff, ⟨k, hk, hc''k⟩, hfarK⟩
  · -- an on-route witness (cases α, α'): the walk from the last common node with the route part
    obtain ⟨-, hsep, hconn, -, -, hmem, -, -, -⟩ := hdat j hj
    obtain ⟨xb, w, hxb, hw, hnd, hch, hlw⟩ := sel_branch_nd (a0 := a0) hsep hconn (hmem _ List.mem_cons_self)
      hb' (List.mem_cons_self : (f j).1 ∈ (f j).1 :: rest j)
    obtain ⟨lv, xb', w', hlv, hdisj, hch', hlw', hw'S, hw'nd, hw'out⟩ := hwalk j hj xb w hxb hw hnd hch
    obtain ⟨hOK, -, -, hpw⟩ := S.cr_of_chain (a1 := a1) hDa hL hdist hdat7 hlv
    -- the witness: the walk, or (span zero) the leaf alone
    obtain ⟨xb'', w'', hwok, hw''⟩ : ∃ xb'' w'', (S3Geom.Wit.on j xb'' w'').OK G.D (G.D - 1 + a0)
        (G.D - 1 + a1) (a1 + 2 - G.D) (S3Geom.CRoute.ofParts n (fun i => (f i).1) rest lv) ∧
        (w'' = w' ∨ w'' = []) := by
      by_cases hrj : rest j = []
      · rw [ite_eq_left hrj] at hdisj
        rcases hdisj with hl | ⟨hxb', hw'0⟩
        · refine ⟨xb', w', ⟨hj, ?_, hch', ?_⟩, Or.inl rfl⟩
          · show if rest j = [] then (if rest j = [] then some (lv j) else none) = some xb'
              else xb' ∈ (f j).1 :: rest j
            rw [ite_eq_left hrj]
            exact hl
          · show a1 + 2 - G.D ≤ G.blockDist (f j).1 (S3Geom.lastOf xb' w')
            rw [hlw', hlw]
            exact hfar
        · have h0span : a1 + 2 - G.D = 0 := by
            have hb'j : b' = (f j).1 := by
              rw [← hlw, ← hlw', hxb', hw'0]
              simp [S3Geom.lastOf]
            rw [hb'j, G.blockDist_self] at hfar
            omega
          refine ⟨lv j, [], ⟨hj, ?_, List.isChain_singleton _, by rw [h0span]; exact Nat.zero_le _⟩, Or.inr rfl⟩
          show if rest j = [] then (if rest j = [] then some (lv j) else none) = some (lv j)
            else lv j ∈ (f j).1 :: rest j
          rw [ite_eq_left hrj, ite_eq_left hrj]
      · rw [ite_eq_right hrj] at hdisj
        refine ⟨xb', w', ⟨hj, ?_, hch', ?_⟩, Or.inl rfl⟩
        · show if rest j = [] then (if rest j = [] then some (lv j) else none) = some xb'
            else xb' ∈ (f j).1 :: rest j
          rw [ite_eq_right hrj]
          exact hdisj
        · show a1 + 2 - G.D ≤ G.blockDist (f j).1 (S3Geom.lastOf xb' w')
          rw [hlw', hlw]
          exact hfar
    have hw''S : ∀ b ∈ w'', b ∈ Sel j := by
      rcases hw'' with rfl | rfl
      · exact hw'S
      · exact fun b hb => absurd hb (by simp)
    have hw''out : ∀ b ∈ w'', b ∉ (f j).1 :: (rest j ++ (if rest j = [] then some (lv j) else none).toList) := by
      rcases hw'' with rfl | rfl
      · exact hw'out
      · exact fun b hb => absurd hb (by simp)
    have hw''pw : w''.Pairwise (fun b b' => G.D ≤ G.blockDist b b') := by
      rcases hw'' with rfl | rfl
      · exact List.Pairwise.imp_of_mem (fun hx hy hxy => hsep _ (hw'S _ hx) _ (hw'S _ hy) hxy) hw'nd
      · exact List.Pairwise.nil
    refine ⟨_, .on j xb'' w'', hOK, hwok, h0, hxlast lv, fun b hb => ?_, ?_⟩
    · rcases List.mem_append.1 hb with hb | hb
      · exact hfamB lv hlv b hb
      · exact hfam j hj b ((hdat7 j hj).1 b (hw''S b hb))
    · exact List.pairwise_append.2 ⟨hpw, hw''pw,
        fun b hb y hy => hsepW lv hlv j hj y (hw''S y hy) (hw''out y hy) b hb⟩
  · -- an off-route witness (case β): the walk in the route cluster `C_x`, a link, and the excursion route
    obtain ⟨jx, p, h, hjx, hp1, ⟨hhP, hhL, -, hhn⟩, hjxc, hhK, hhoff, hhd⟩ := S.exc_chain he hfch hoff hk hc''k
    -- the excursion chain without its first pair, its last exit replaced by `c''`
    obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → G.Block × G.Block, (∀ t, t ≠ p - 1 → g t = h (t + 1)) ∧
        g (p - 1) = ((h p).1, c'') :=
      ⟨fun t => if t = p - 1 then ((h p).1, c'') else h (t + 1), fun t ht => by simp [ht], by simp⟩
    have hclp : S.cluster E a0 (h p).1 = S.cluster E a0 k := by
      have := (hhP p le_rfl).2.2
      rwa [hhn] at this
    have hc''bad : S.badD E c'' := S.badD_of_lev1 hc''1
    have hclc : S.cluster E a0 c'' = S.cluster E a0 k := S3Geom.comp_eq_of_mem hc''k
    have hg1st : ∀ t ≤ p - 1, (g t).1 = (h (t + 1)).1 := by
      intro t ht
      rcases eq_or_ne t (p - 1) with h' | h'
      · rw [h', hg2, show p - 1 + 1 = p by omega]
      · rw [hg1 t h']
    have hgP : ∀ t ≤ p - 1, S.PairOK a0 E (g t) := by
      intro t ht
      rcases eq_or_ne t (p - 1) with h' | h'
      · rw [h', hg2]
        exact ⟨(hhP p le_rfl).1, hc''bad, hclp.trans hclc.symm⟩
      · rw [hg1 t h']
        exact hhP _ (by omega)
    have hgL : ∀ t < p - 1, S.LinkOK a0 a1 E (g t).2 (g (t + 1)).1 := by
      intro t ht
      rw [hg1 t (by omega), hg1st (t + 1) (by omega)]
      exact hhL (t + 1) (by omega)
    have hg0 : (g 0).1 = (h 1).1 := hg1st 0 (by omega)
    have hh1lev : (h 1).1 ∈ S.lev1 a0 E := by
      have := (hhL 0 (by omega)).2.1
      simpa using this
    have hgd : ∀ i j, i < j → j ≤ p - 1 → S.cluster E a0 (g i).1 ≠ S.cluster E a0 (g j).1 := by
      intro i j hij hj
      rw [hg1st i (by omega), hg1st j hj]
      exact hhd (i + 1) (j + 1) (by omega) (by omega)
    have hgfam : ∀ i ≤ p - 1, ∀ c ∈ S.cluster E a0 (g i).1, c ∈ S.family a0 a1 E e := by
      intro i hi c hc
      rw [hg1st i hi] at hc
      exact S.lev1comp_cluster_family he (hhK (i + 1) (by omega)).1 c hc
    have hgrow : ∀ i ≤ p - 1, ∀ c ∈ S.cluster E a0 (g i).1, hs a1 < c.2.val ∧ c.2.val + 1 + hs a1 < G.ny :=
      fun i hi c hc => hint c (hgfam i hi c hc)
    obtain ⟨Sel', rest', sEnd', -, hdat', -⟩ := S.route_of_chain ha0 hD1 hDa hh1lev hgP hgL hg0 hgd hgrow
    have hdat7' : ∀ i ≤ p - 1, (∀ b ∈ Sel' i, b ∈ S.cluster E a0 (g i).1) ∧
        (∀ b ∈ Sel' i, ∀ b' ∈ Sel' i, b ≠ b' → G.D ≤ G.blockDist b b') ∧
        ((g i).1 :: rest' i).Nodup ∧ (∀ b ∈ (g i).1 :: rest' i, b ∈ Sel' i) ∧
        List.IsChain (fun y z => y ≠ z ∧ G.blockDist y z ≤ G.D - 1 + a0) ((g i).1 :: rest' i) ∧
        ((g i).1 :: rest' i).getLast? = some (sEnd' i) ∧ G.blockDist (g i).2 (sEnd' i) ≤ G.D - 1 := by
      intro i hi
      obtain ⟨h1, h2, -, -, h5, h6, h7, h8, h9⟩ := hdat' i hi
      exact ⟨h1, h2, h5, h6, h7, h8, h9⟩
    have hgroot1 : ∀ i ≤ p - 1, (g i).1 ∈ S.lev1 a0 E := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with h' | h'
      · rw [h', hg0]
        exact hh1lev
      · have := (hgL (i - 1) (by omega)).2.1
        rwa [show i - 1 + 1 = i by omega] at this
    -- (W0) leaves at the excursion clusters
    have hleafE' : ∀ i, ∃ l : G.Block, i ≤ p - 1 → l ∈ Sel' i ∧ l ≠ (g i).1 ∧
        G.blockDist (g i).1 l ≤ G.D - 1 + a0 := by
      intro i
      by_cases hi : i ≤ p - 1
      · obtain ⟨-, -, hconn', hcov', -, hmem', -, -, -⟩ := hdat' i hi
        obtain ⟨l, hlS, hl⟩ := S.sel_leaf ha0 hDa (hgroot1 i hi) (hintF _ (hgfam i hi)) hconn' hcov'
          (hmem' _ List.mem_cons_self)
        exact ⟨l, fun _ => ⟨hlS, hl⟩⟩
      · exact ⟨e, fun hc => absurd hc hi⟩
    choose leaf' hleaf' using hleafE'
    obtain ⟨hexOK, hexlast, hexsel, hexpw⟩ := S.cr_of_chain (a1 := a1) (lv := leaf') hDa hgL hgd hdat7'
      (fun i hi _ => hleaf' i hi)
    -- the last excursion part spans at least `a1 + 2 - D`
    have hspan : a1 + 2 - G.D ≤ G.blockDist (g (p - 1)).1 (sEnd' (p - 1)) := by
      have hcov' := (hdat7' (p - 1) le_rfl).2.2.2.2.2.2
      rw [hg2] at hcov'
      dsimp only at hcov'
      have hf := hfarK (h p).1 (hhK p le_rfl).1
      have t := G.blockDist_triangle (h p).1 (sEnd' (p - 1)) c''
      rw [G.blockDist_comm (sEnd' (p - 1))] at t
      rw [hg1st (p - 1) le_rfl, show p - 1 + 1 = p by omega]
      omega
    -- the walk in `C_x` to the cover of the excursion's first exit
    obtain ⟨hSKx, hsepx, hconnx, hcovx, -, hmemx, -, -, -⟩ := hdat jx hjx
    have hh0x : (h 0).2 ∈ S.cluster E a0 (f jx).1 := by
      have hc0 := (hhP 0 (by omega)).2.2
      have h1 : S.cluster E a0 (h 0).1 = S.cluster E a0 (f jx).1 := S3Geom.comp_eq_of_mem hjxc
      rw [← h1, hc0]
      exact S.mem_cluster_self (hhP 0 (by omega)).2.1
    obtain ⟨sx, hsxS, hsxd⟩ := hcovx (h 0).2 hh0x
    obtain ⟨xb, w, hxb, hw, hnd, hch, hlw⟩ := sel_branch_nd (a0 := a0) hsepx hconnx
      (hmemx _ List.mem_cons_self) hsxS (List.mem_cons_self : (f jx).1 ∈ (f jx).1 :: rest jx)
    obtain ⟨lv, xb', w', hlv, hdisj, hch', hlw', hw'S, hw'nd, hw'out⟩ := hwalk jx hjx xb w hxb hw hnd hch
    obtain ⟨hOK, -, -, hpw⟩ := S.cr_of_chain (a1 := a1) hDa hL hdist hdat7 hlv
    -- the link from the end of the walk to the excursion
    have hh1K : (h 1).1 ∈ S.cluster E a0 (h 1).1 := S.mem_cluster_self (hhP 1 hp1).1
    have hsxK : sx ∈ S.cluster E a0 (f jx).1 := hSKx sx hsxS
    have hlo : G.D ≤ G.blockDist sx (h 1).1 :=
      S.sep_of_cluster_ne hDa hsxK hh1K (fun hc => hhoff 1 le_rfl hp1 jx hjx hc.symm)
    have hhi : G.blockDist sx (h 1).1 ≤ G.D - 1 + a1 := by
      have t := G.blockDist_triangle sx (h 0).2 (h 1).1
      have t2 : G.blockDist (h 0).2 (h 1).1 ≤ a1 := (hhL 0 (by omega)).2.2
      rw [G.blockDist_comm sx (h 0).2] at t
      omega
    have hexK : ∀ z ∈ (S3Geom.CRoute.ofParts (p - 1) (fun i => (g i).1) rest' leaf').blocks,
        ∃ i ≤ p - 1, z ∈ S.cluster E a0 (h (i + 1)).1 := by
      intro z hz
      obtain ⟨i, hi, hzi⟩ := hexsel z hz
      exact ⟨i, hi, by rw [← hg1st i hi]; exact (hdat7' i hi).1 z hzi⟩
    have hw'pw : w'.Pairwise (fun b b' => G.D ≤ G.blockDist b b') :=
      List.Pairwise.imp_of_mem (fun hx hy hxy => hsepx _ (hw'S _ hx) _ (hw'S _ hy) hxy) hw'nd
    refine ⟨_, .off jx xb' w' (S3Geom.CRoute.ofParts (p - 1) (fun i => (g i).1) rest' leaf'), hOK,
      ⟨hjx, hdisj, hch', hexOK, ?_, ?_, ?_⟩, h0, hxlast lv, fun b hb => ?_, ?_⟩
    · show G.D ≤ G.blockDist (S3Geom.lastOf xb' w') (g 0).1
      rw [hlw', hlw, hg0]
      exact hlo
    · show G.blockDist (S3Geom.lastOf xb' w') (g 0).1 ≤ G.D - 1 + a1
      rw [hlw', hlw, hg0]
      exact hhi
    · rw [hexlast]
      exact hspan
    · rcases List.mem_append.1 hb with hb | hb
      · exact hfamB lv hlv b hb
      · rcases List.mem_append.1 hb with hb | hb
        · exact hfam jx hjx b (hSKx b (hw'S b hb))
        · obtain ⟨i, hi, hbi⟩ := hexsel b hb
          exact hgfam i hi b ((hdat7' i hi).1 b hbi)
    · refine List.pairwise_append.2 ⟨hpw, List.pairwise_append.2 ⟨hw'pw, hexpw, fun y hy z hz => ?_⟩,
        fun b hb y hy => ?_⟩
      · obtain ⟨i, hi, hzK⟩ := hexK z hz
        exact S.sep_of_cluster_ne hDa (hSKx y (hw'S y hy)) hzK
          (fun hc => hhoff (i + 1) (by omega) (by omega) jx hjx hc.symm)
      · rcases List.mem_append.1 hy with hy | hy
        · exact hsepW lv hlv jx hjx y (hw'S y hy) (hw'out y hy) b hb
        · obtain ⟨i, hi, hbi⟩ := hmemB lv b hb
          obtain ⟨i', hi', hyK⟩ := hexK y hy
          exact S.sep_of_cluster_ne hDa ((hdat7 i hi).1 b (hclS lv hlv i hi b hbi)) hyK
            (fun hc => hhoff (i' + 1) (by omega) (by omega) i hi hc.symm)

/-! ### Existence: the stations of a T2 path -/

/-- A family with a block in each strip is a T1 family. -/
theorem T1_of_fam {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {Fm : Set G.Block} (hFm : Fm ∈ S.families a0 a1 E)
    (h1 : ∃ c ∈ Fm, c.2.val ≤ hs a1) (h2 : ∃ c ∈ Fm, G.ny ≤ c.2.val + 1 + hs a1) : S.T1 a0 a1 E := by
  obtain ⟨c0, hc0, rfl⟩ := (S.mem_families).1 hFm
  exact ⟨c0, hc0, h1, h2⟩

/-- Without T1, the two ends of a T2 path are distinct nodes. -/
theorem ends_ne {a0 a1 : ℕ} {E : G.Ed → ZMod 2} (hT1 : ¬ S.T1 a0 a1 E) {x y : G.GNode}
    (hx : x = .inr (.inl false) ∨ S.botFam a0 a1 E x) (hy : y = .inr (.inl true) ∨ S.topFam a0 a1 E y) :
    x ≠ y := by
  rintro rfl
  rcases x with u | b | F
  · rcases hx with h | h
    · exact absurd h (by simp)
    · exact h
  · rcases hx with h | h
    · rcases hy with h' | h'
      · rw [h] at h'
        exact absurd h' (by simp)
      · exact h'
    · exact h
  · rcases hx with h | ⟨hF, c1, hc1, hr1⟩
    · exact absurd h (by simp)
    · rcases hy with h' | ⟨-, c2, hc2, hr2⟩
      · exact absurd h' (by simp)
      · exact hT1 (S.T1_of_fam hF ⟨c1, hc1, hr1⟩ ⟨c2, hc2, hr2⟩)

/-- **No two adjacent non-check nodes** on a T2 path without T1: families are not adjacent to each other, the two
boundaries are not adjacent, and a family adjacent to a boundary has a block in that strip, so it would be the other
end, a T1 family. -/
theorem no_adj_nonchk {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (ha01 : a0 ≤ a1) {Z : Solver G} {E : G.Ed → ZMod 2}
    (hT1 : ¬ S.T1 a0 a1 E) {l : List G.GNode} {x y : G.GNode}
    (hy : y = .inr (.inl true) ∨ S.topFam a0 a1 E y) (hx : x = .inr (.inl false) ∨ S.botFam a0 a1 E x)
    (hbd : ∀ b : Bool, (.inr (.inl b) : G.GNode) ∈ l → (.inr (.inl b) : G.GNode) = x ∨ (.inr (.inl b) : G.GNode) = y)
    (hint : ∀ z ∈ l, z ≠ x → z ≠ y → S.interFam a0 a1 E z)
    {z1 z2 : G.GNode} (hz1 : z1 ∈ l) (hz2 : z2 ∈ l) (hadj : S.gadj a0 a1 Z E z1 z2)
    (h1 : ¬ isChk z1) (h2 : ¬ isChk z2) : False := by
  have key : ∀ {F : Set G.Block} {b : Bool}, (.inr (.inr F) : G.GNode) ∈ l → (.inr (.inl b) : G.GNode) ∈ l →
      S.gadj a0 a1 Z E (.inr (.inr F)) (.inr (.inl b)) → False := by
    intro F b hF hb hg
    have hg0 : S.gadj0 a0 a1 Z E (.inr (.inr F)) (.inr (.inl b)) := by
      rcases hg with hg | hg
      · exact hg
      · rcases b with _ | _ <;> simp [gadj0] at hg
    rcases b with _ | _
    · obtain ⟨hFm, hpc⟩ := hg0
      obtain ⟨c1, hc1, hr1⟩ := S.strip_bot_of_pcls ha0 ha01 Z hFm hpc
      have hbx : (.inr (.inl false) : G.GNode) = x := by
        rcases hbd false hb with h | h
        · exact h
        · exfalso
          rcases hy with h' | h'
          · rw [← h] at h'
            simp at h'
          · rw [← h] at h'
            exact h'
      by_cases hFx : (.inr (.inr F) : G.GNode) = x
      · rw [← hbx] at hFx
        simp at hFx
      by_cases hFy : (.inr (.inr F) : G.GNode) = y
      · rw [← hFy] at hy
        rcases hy with h' | ⟨-, c2, hc2, hr2⟩
        · simp at h'
        · exact hT1 (S.T1_of_fam hFm ⟨c1, hc1, hr1⟩ ⟨c2, hc2, hr2⟩)
      · obtain ⟨-, hall⟩ := hint _ hF hFx hFy
        have := hall c1 hc1
        omega
    · obtain ⟨hFm, hpc⟩ := hg0
      obtain ⟨c2, hc2, hr2⟩ := S.strip_top_of_pclsT ha0 ha01 Z hFm hpc
      have hby : (.inr (.inl true) : G.GNode) = y := by
        rcases hbd true hb with h | h
        · exfalso
          rcases hx with h' | h'
          · rw [← h] at h'
            simp at h'
          · rw [← h] at h'
            exact h'
        · exact h
      by_cases hFy : (.inr (.inr F) : G.GNode) = y
      · rw [← hby] at hFy
        simp at hFy
      by_cases hFx : (.inr (.inr F) : G.GNode) = x
      · rw [← hFx] at hx
        rcases hx with h' | ⟨-, c1, hc1, hr1⟩
        · simp at h'
        · exact hT1 (S.T1_of_fam hFm ⟨c1, hc1, hr1⟩ ⟨c2, hc2, hr2⟩)
      · obtain ⟨-, hall⟩ := hint _ hF hFx hFy
        have := hall c2 hc2
        omega
  rcases z1 with u1 | b1 | F1
  · exact h1 ⟨u1, rfl⟩
  · rcases z2 with u2 | b2 | F2
    · exact h2 ⟨u2, rfl⟩
    · rcases hadj with hg | hg <;> rcases b1 with _ | _ <;> rcases b2 with _ | _ <;> simp [gadj0] at hg
    · exact key hz2 hz1 (Or.symm hadj)
  · rcases z2 with u2 | b2 | F2
    · exact h2 ⟨u2, rfl⟩
    · exact key hz1 hz2 hadj
    · exact S.not_gadj_fam_fam hadj

/-- **The stations of a T2 path** (the indexing of `metric_stations`): positions `p 0 = 0 < p 1 < … < p (m+1) =
length - 1` of the end nodes and the intermediate families, the entry checks `u i` before and the exit checks `v i`
after them, with at least one check between consecutive stations. -/
theorem t2_stations {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (ha01 : a0 ≤ a1) {Z : Solver G} {E : G.Ed → ZMod 2}
    (hT1 : ¬ S.T1 a0 a1 E) {l : List G.GNode} {x y : G.GNode} (hhd : l.head? = some x)
    (hlst : l.getLast? = some y) (hnd : l.Nodup) (hch : List.IsChain (S.gadj a0 a1 Z E) l)
    (hx : x = .inr (.inl false) ∨ S.botFam a0 a1 E x) (hy : y = .inr (.inl true) ∨ S.topFam a0 a1 E y)
    (hbd : ∀ b : Bool, (.inr (.inl b) : G.GNode) ∈ l → (.inr (.inl b) : G.GNode) = x ∨ (.inr (.inl b) : G.GNode) = y)
    (hint : ∀ z ∈ l, z ≠ x → z ≠ y → S.interFam a0 a1 E z) :
    ∃ (m : ℕ) (p : ℕ → ℕ) (u v : ℕ → G.V), 2 ≤ l.length ∧
      (∀ i j, i < j → j ≤ m + 1 → p i < p j) ∧ p 0 = 0 ∧ p (m + 1) = l.length - 1 ∧
      (∀ i, 1 ≤ i → i ≤ m → isFam (nd l (p i))) ∧
      (∀ k, (∀ i ≤ m + 1, k ≠ p i) → ¬ isFam (nd l k)) ∧
      (∀ i, 1 ≤ i → i ≤ m + 1 → nd l (p i - 1) = .inl (u i)) ∧
      (∀ i ≤ m, nd l (p i + 1) = .inl (v i)) ∧
      (∀ i ≤ m, p i + 1 < p (i + 1)) := by
  have hl : l ≠ [] := by
    rintro rfl
    simp at hhd
  have hx0 : nd l 0 = x := nd_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd)
  have hyl : nd l (l.length - 1) = y := nd_of_getElem? (by rw [← List.getLast?_eq_getElem?]; exact hlst)
  have hlen : 2 ≤ l.length := by
    by_contra hlt
    have hl1 : l.length = 1 := by
      have := List.length_pos_of_ne_nil hl
      omega
    apply S.ends_ne hT1 hx hy
    rw [← hx0, ← hyl, hl1]
  have hmem : ∀ k, k < l.length → nd l k ∈ l := by
    intro k hk
    rw [nd_of_getElem? (List.getElem?_eq_getElem hk)]
    exact List.getElem_mem hk
  have hxnc : ¬ isChk x := by
    rintro ⟨u, rfl⟩
    rcases hx with h | h
    · simp at h
    · exact h
  have hync : ¬ isChk y := by
    rintro ⟨u, rfl⟩
    rcases hy with h | h
    · simp at h
    · exact h
  have hfnc : ∀ z : G.GNode, isFam z → ¬ isChk z := by
    rintro z ⟨F, rfl⟩ ⟨u, hu⟩
    simp at hu
  -- the family positions strictly inside, and the stations
  set FP : List ℕ := (List.range l.length).filter
    (fun k => decide (0 < k ∧ k + 1 < l.length ∧ isFam (nd l k))) with hFP
  have hFPmem : ∀ k, k ∈ FP ↔ 0 < k ∧ k + 1 < l.length ∧ isFam (nd l k) := by
    intro k
    simp only [hFP, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨by omega, h⟩
  have hFPs : FP.Pairwise (· < ·) := List.pairwise_lt_range.filter _
  set SL : List ℕ := 0 :: (FP ++ [l.length - 1]) with hSL
  have hSLs : SL.Pairwise (· < ·) := by
    rw [hSL, List.pairwise_cons, List.pairwise_append]
    refine ⟨fun a ha => ?_, hFPs, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    · rcases List.mem_append.1 ha with ha | ha
      · exact ((hFPmem a).1 ha).1
      · rw [List.mem_singleton.1 ha]
        omega
    · rw [List.mem_singleton.1 hb]
      have := ((hFPmem a).1 ha).2.1
      omega
  have hSLlen : SL.length = FP.length + 2 := by simp [hSL]
  set m := FP.length with hm
  set p : ℕ → ℕ := fun i => SL.getD i 0 with hpdef
  have hpget : ∀ i (hi : i < SL.length), p i = SL[i] := fun i hi => List.getD_eq_getElem _ _ hi
  have hp : ∀ i j, i < j → j ≤ m + 1 → p i < p j := by
    intro i j hij hj
    rw [hpget i (by omega), hpget j (by omega)]
    exact List.pairwise_iff_getElem.1 hSLs i j (by omega) (by omega) hij
  have hpmono : ∀ i j, i ≤ j → j ≤ m + 1 → p i ≤ p j := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact (hp i j h hj).le
  have hp0 : p 0 = 0 := by simp [hpdef, hSL]
  have hpl : p (m + 1) = l.length - 1 := by
    simp only [hpdef, hSL, List.getD_cons_succ]
    rw [List.getD_append_right _ _ _ _ (le_of_eq rfl)]
    simp
  have hpin : ∀ i, 1 ≤ i → i ≤ m → p i ∈ FP := by
    intro i hi1 him
    have hpi : p i = FP[i - 1] := by
      simp only [hpdef, hSL]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [List.getD_cons_succ, List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      rfl
    rw [hpi]
    exact List.getElem_mem _
  have hFPp : ∀ k ∈ FP, ∃ i, 1 ≤ i ∧ i ≤ m ∧ p i = k := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hk
    refine ⟨j + 1, by omega, by omega, ?_⟩
    simp only [hpdef, hSL]
    rw [List.getD_cons_succ, List.getD_append _ _ _ _ hj, List.getD_eq_getElem _ _ hj]
  have hpfam : ∀ i, 1 ≤ i → i ≤ m → isFam (nd l (p i)) := fun i hi1 him => ((hFPmem _).1 (hpin i hi1 him)).2.2
  have hnofam : ∀ k, (∀ i ≤ m + 1, k ≠ p i) → ¬ isFam (nd l k) := by
    intro k hk hf
    by_cases hkl : k < l.length
    · by_cases hk0 : k = 0
      · exact hk 0 (Nat.zero_le _) (by rw [hk0, hp0])
      by_cases hkL : k = l.length - 1
      · exact hk (m + 1) le_rfl (by rw [hkL, hpl])
      obtain ⟨i, hi1, him, hi⟩ := hFPp k ((hFPmem k).2 ⟨by omega, by omega, hf⟩)
      exact hk i (by omega) hi.symm
    · obtain ⟨F, hF⟩ := hf
      simp [nd, List.getElem?_eq_none (by omega : l.length ≤ k)] at hF
  -- nodes at stations are not checks
  have hstnc : ∀ i ≤ m + 1, ¬ isChk (nd l (p i)) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, hp0, hx0]
      exact hxnc
    · rcases eq_or_lt_of_le hi with h' | h'
      · rw [h', hpl, hyl]
        exact hync
      · exact hfnc _ (hpfam i h (by omega))
  have hplt : ∀ i ≤ m + 1, p i < l.length := by
    intro i hi
    have := hpmono i (m + 1) hi le_rfl
    rw [hpl] at this
    omega
  -- at least one check between consecutive stations
  have hgap : ∀ i ≤ m, p i + 1 < p (i + 1) := by
    intro i hi
    by_contra hng
    have hlt := hp i (i + 1) (by omega) (by omega)
    have heq : p (i + 1) = p i + 1 := by omega
    have hadj := chain_step hch (getElem?_nd (hplt i (by omega)))
      (by rw [← heq]; exact getElem?_nd (hplt (i + 1) (by omega)))
    exact S.no_adj_nonchk ha0 ha01 hT1 hy hx hbd hint (hmem _ (hplt i (by omega)))
      (hmem _ (hplt (i + 1) (by omega))) hadj (hstnc i (by omega)) (hstnc (i + 1) (by omega))
  -- positions strictly between consecutive stations hold checks
  have hbetween : ∀ i ≤ m, ∀ k, p i < k → k < p (i + 1) → isChk (nd l k) := by
    intro i hi k hk1 hk2
    have hkl : k < l.length := by
      have := hplt (i + 1) (by omega)
      omega
    have hns : ∀ j ≤ m + 1, k ≠ p j := by
      intro j hj hkj
      rw [hkj] at hk1 hk2
      by_cases hji : j ≤ i
      · have := hpmono j i hji (by omega)
        omega
      · have := hpmono (i + 1) j (by omega) hj
        omega
    rcases hz : nd l k with u | b | F
    · exact ⟨u, rfl⟩
    · exfalso
      have hbmem : (.inr (.inl b) : G.GNode) ∈ l := by
        rw [← hz]
        exact hmem k hkl
      rcases hbd b hbmem with h | h
      · rw [← hz, ← hx0, nd_eq_iff hnd hkl (by omega)] at h
        exact hns 0 (Nat.zero_le _) (by rw [h, hp0])
      · rw [← hz, ← hyl, nd_eq_iff hnd hkl (by omega)] at h
        exact hns (m + 1) le_rfl (by rw [h, hpl])
    · exact absurd ⟨F, hz⟩ (hnofam k hns)
  refine ⟨m, p, fun i => gchk (nd l (p i - 1)), fun i => gchk (nd l (p i + 1)), hlen, hp, hp0, hpl, hpfam, hnofam,
    fun i hi1 him => ?_, fun i hi => ?_, hgap⟩
  · have hg := hgap (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at hg
    exact nd_isChk (hbetween (i - 1) (by omega) _ (by omega) (by rw [show i - 1 + 1 = i by omega]; omega))
  · exact nd_isChk (hbetween i hi _ (by omega) (hgap i hi))

/-! ### Existence: assembly -/

/-- The block set of a family node (empty for the other nodes). -/
def famOf : G.GNode → Set G.Block
  | .inr (.inr Fm) => Fm
  | _ => ∅

/-- A bad block (convention (i)) in the sampled rows is bad. -/
theorem bad_of_badD_sampled {E : G.Ed → ZMod 2} {c : G.Block} (hc : S.badD E c) (h1 : 2 ≤ c.2.val)
    (h2 : c.2.val + 3 ≤ G.ny) : S.bad E c := by
  rcases hc with hdecl | hbad
  · exfalso
    rcases hdecl with h | h <;> omega
  · exact hbad

/-- An odd check of `Ω` lies in a level-1 block of an unresolved level-1 component (property (R)). -/
theorem om_lev1 {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {u : G.V} (hu : S.om a0 a1 E u ≠ 0) :
    G.blockOf u ∈ S.lev1 a0 E ∧ ¬ G.resolved (S.resid E) ((a1 + 1) / 2) (S.lev1comp a0 a1 E (G.blockOf u)) :=
  omega_mem_level1 hu

/-- Blocks of distinct families are at least `D` apart. -/
theorem sep_of_fam_ne {a0 a1 : ℕ} (hDa : G.D ≤ a0 + 1) {E : G.Ed → ZMod 2} {F F' : Set G.Block}
    (hF : F ∈ S.families a0 a1 E) (hF' : F' ∈ S.families a0 a1 E) (hne : F ≠ F') {b b' : G.Block}
    (hb : b ∈ F) (hb' : b' ∈ F') : G.D ≤ G.blockDist b b' := by
  obtain ⟨c0, hc0, rfl⟩ := (S.mem_families).1 hF
  have hbb : S.badD E b := S.badD_of_mem_family hb
  obtain ⟨c0', hc0', rfl⟩ := (S.mem_families).1 hF'
  have hbb' : S.badD E b' := S.badD_of_mem_family hb'
  refine S.sep_of_cluster_ne hDa (S.mem_cluster_self hbb) (S.mem_cluster_self hbb') fun hc => hne ?_
  have hb'b : b' ∈ S.cluster E a0 b := by
    rw [hc]
    exact S.mem_cluster_self hbb'
  have hb'F : b' ∈ S.family a0 a1 E c0 := by
    rw [← S.family_eq_of_mem hb]
    exact S.mem_family_of_cluster hbb hb'b
  exact S.families_eq_of_mem hF hF' hb'F hb'

theorem bl1_triangle (b c d : G.Block) : S3Geom.bl1 b d ≤ S3Geom.bl1 b c + S3Geom.bl1 c d := by
  simp only [S3Geom.bl1, ndist]
  omega

theorem bl1_le_blockDist (b b' : G.Block) : S3Geom.bl1 b b' ≤ 2 * G.blockDist b b' := by
  simp only [S3Geom.bl1, S3Geom.blockDist]
  have h1 := le_max_left (ndist b.1.val b'.1.val) (ndist b.2.val b'.2.val)
  have h2 := le_max_right (ndist b.1.val b'.1.val) (ndist b.2.val b'.2.val)
  omega

theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- The exchange inequality in station form, divided by `wmin L`: the form of (X) in `T2Sk.OK`. -/
theorem metric_convert {m L D : ℕ} (hL : 1 ≤ L) {wmin wmax wh : ℝ} (hmin0 : 0 < wmin)
    (hmax0 : 0 ≤ wmax) {A A0 B B0 vy hy r0 rt ny : ℝ}
    (hA : A ≤ A0 + (m + 1) * (2 * ((D : ℝ) - 1))) (hB : B0 ≤ B + m * (2 * ((D : ℝ) - 1)))
    (hvy : vy ≤ L * (r0 + D)) (hhy : hy ≤ L * (ny - rt))
    (hmet : wmin * ((L : ℝ) * A0) ≤ wmax * ((L : ℝ) * B0) + (wmin * (m + 1) + wmax * m) * (2 * ((L : ℝ) - 1)) +
      wmax * vy + wmax * hy + 2 * wh) :
    A ≤ wmax / wmin * B + 2 * D * (m + 1) + 2 * D * (wmax / wmin) * m + wmax / wmin * (r0 + D) +
      wmax / wmin * (ny - rt) + 2 * wh / (wmin * L) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hWL : 0 < wmin * L := mul_pos hmin0 (by linarith)
  rw [← mul_le_mul_iff_right₀ hWL]
  have e1 : wmin * L * (wmax / wmin * B + 2 * D * (m + 1) + 2 * D * (wmax / wmin) * m + wmax / wmin * (r0 + D) +
      wmax / wmin * (ny - rt) + 2 * wh / (wmin * L)) =
      wmax * L * B + 2 * D * wmin * L * (m + 1) + 2 * D * wmax * L * m + wmax * L * (r0 + D) +
        wmax * L * (ny - rt) + 2 * wh := by
    field_simp
  rw [e1]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 := mul_le_mul_of_nonneg_left hA hWL.le
  have h2 := mul_le_mul_of_nonneg_left hB (mul_nonneg hmax0 (by linarith : (0 : ℝ) ≤ L))
  have h3 := mul_le_mul_of_nonneg_left hvy hmax0
  have h4 := mul_le_mul_of_nonneg_left hhy hmax0
  have h5 : 0 ≤ wmin * ((m : ℝ) + 1) := mul_nonneg hmin0.le (by linarith)
  have h6 : 0 ≤ wmax * (m : ℝ) := mul_nonneg hmax0 hm0
  nlinarith [h1, h2, h3, h4, h5, h6, hmet]

/-- **T2 skeleton existence** (deterministic part, with the end routes): for `a0 ≥ 2`, `1 ≤ D ≤ a0 + 1`,
`a0 ≤ a1` and a solver whose weights are nonnegative, at least `wmin > 0` and at most `wmax` on bulk edges and at most
`wh` on half-edges, every error in the T2 event without T1 has a valid skeleton (metric ratio `wmax / wmin`,
boundary constant `2 wh / (wmin L)`) whose counted blocks are all bad. -/
theorem t2SkelExistsOn {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (hD1 : 1 ≤ G.D) (hDa : G.D ≤ a0 + 1) (ha01 : a0 ≤ a1)
    (Z : Solver G) (hwt0 : ∀ e, 0 ≤ Z.wt e) {wmin wmax wh : ℝ} (hmin0 : 0 < wmin) (hmax0 : 0 ≤ wmax)
    (hwh0 : 0 ≤ wh) (hmin : ∀ e, S3Geom.isBulk e → wmin ≤ Z.wt e) (hmax : ∀ e, S3Geom.isBulk e → Z.wt e ≤ wmax)
    (hbot : ∀ x, Z.wt (.bot x) ≤ wh) (htop : ∀ x, Z.wt (.top x) ≤ wh) :
    S.T2SkelExistsOn a0 a1 Z (wmax / wmin) (2 * wh / (wmin * G.L)) := by
  intro E hT2 hT1
  obtain ⟨l, x, y, hhd, hlst, hnd, hch, hx, hy, hbd, hint⟩ := hT2
  obtain ⟨m, p, u, v, hlen, hp, hp0, hpl, hpfam, hnofam, hu, hv, hgap⟩ :=
    S.t2_stations ha0 ha01 hT1 hhd hlst hnd hch hx hy hbd hint
  have hmet := S.metric_stations_block Z hwt0 hmin0.le hmax0 hwh0 hmin hmax hbot htop hhd hlst hnd hch hx hy hbd
    m p u v hp hp0 hpl hpfam hnofam hu hv
  have hhs1 : 1 ≤ hs a1 := by simp [hs]
  have hx0 : nd l 0 = x := nd_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd)
  have hyl : nd l (l.length - 1) = y := nd_of_getElem? (by rw [← List.getLast?_eq_getElem?]; exact hlst)
  have hpmono : ∀ i j, i ≤ j → j ≤ m + 1 → p i ≤ p j := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact (hp i j h hj).le
  have hplt : ∀ i ≤ m + 1, p i < l.length := by
    intro i hi
    have := hpmono i (m + 1) hi le_rfl
    rw [hpl] at this
    omega
  have hppos : ∀ i, 1 ≤ i → i ≤ m + 1 → 0 < p i := by
    intro i hi1 hi
    have := hp 0 i (by omega) hi
    omega
  have hmem : ∀ k, k < l.length → nd l k ∈ l := by
    intro k hk
    rw [nd_of_getElem? (List.getElem?_eq_getElem hk)]
    exact List.getElem_mem hk
  -- a station and its checks
  have hadjU : ∀ i, 1 ≤ i → i ≤ m + 1 → S.gadj a0 a1 Z E (.inl (u i)) (nd l (p i)) := by
    intro i hi1 hi
    have h1 : l[p i - 1]? = some (.inl (u i)) := by
      rw [← hu i hi1 hi]
      exact getElem?_nd (by have := hplt i hi; omega)
    have h2 : l[p i - 1 + 1]? = some (nd l (p i)) := by
      rw [show p i - 1 + 1 = p i by have := hppos i hi1 hi; omega]
      exact getElem?_nd (hplt i hi)
    exact chain_step hch h1 h2
  have hadjV : ∀ i ≤ m, S.gadj a0 a1 Z E (nd l (p i)) (.inl (v i)) := by
    intro i hi
    have h2 : l[p i + 1]? = some (.inl (v i)) := by
      rw [← hv i hi]
      exact getElem?_nd (by have := hgap i hi; have := hplt (i + 1) (by omega); omega)
    exact chain_step hch (getElem?_nd (hplt i (by omega))) h2
  -- the intermediate families
  have hFex : ∀ i, ∃ F : Set G.Block, 1 ≤ i → i ≤ m → nd l (p i) = .inr (.inr F) := by
    intro i
    by_cases h : 1 ≤ i ∧ i ≤ m
    · obtain ⟨F, hF⟩ := hpfam i h.1 h.2
      exact ⟨F, fun _ _ => hF⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose F hF using hFex
  have hst : ∀ i, 1 ≤ i → i ≤ m → F i ∈ S.families a0 a1 E ∧ G.blockOf (u i) ∈ F i ∧ S.om a0 a1 E (u i) ≠ 0 ∧
      G.blockOf (v i) ∈ F i ∧ S.om a0 a1 E (v i) ≠ 0 ∧
      (∀ c ∈ F i, hs a1 < c.2.val ∧ c.2.val + 1 + hs a1 < G.ny) := by
    intro i hi1 hi
    have hu' := hadjU i hi1 (by omega)
    have hv' := hadjV i (by omega)
    rw [hF i hi1 hi] at hu' hv'
    obtain ⟨hFm, hbu, hou⟩ := S.gadj_check_fam hu'
    obtain ⟨-, hbv, hov⟩ := S.gadj_fam_check hv'
    refine ⟨hFm, hbu, hou, hbv, hov, ?_⟩
    have hne0 : nd l (p i) ≠ x := by
      rw [← hx0, Ne, nd_eq_iff hnd (hplt i (by omega)) (by omega)]
      have := hppos i hi1 (by omega)
      omega
    have hneL : nd l (p i) ≠ y := by
      rw [← hyl, Ne, nd_eq_iff hnd (hplt i (by omega)) (by omega)]
      have := hp i (m + 1) (by omega) le_rfl
      omega
    have := hint _ (hmem _ (hplt i (by omega))) hne0 hneL
    rw [hF i hi1 hi] at this
    exact this.2
  -- the skeleton unit of each intermediate family
  have hunitE : ∀ i, ∃ (cr : G.CRoute) (wt : G.Wit), 1 ≤ i → i ≤ m →
      cr.OK G.D (G.D - 1 + a0) (G.D - 1 + a1) ∧ wt.OK G.D (G.D - 1 + a0) (G.D - 1 + a1) (a1 + 2 - G.D) cr ∧
      cr.r 0 = G.blockOf (u i) ∧ G.blockDist (G.blockOf (v i)) cr.last ≤ G.D - 1 ∧
      (∀ b ∈ cr.blocks ++ wt.blocks, b ∈ F i) ∧
      (cr.blocks ++ wt.blocks).Pairwise (fun b b' => G.D ≤ G.blockDist b b') := by
    intro i
    by_cases h : 1 ≤ i ∧ i ≤ m
    · obtain ⟨hFm, hbu, hou, hbv, hov, hmid⟩ := hst i h.1 h.2
      have hfe : S.family a0 a1 E (G.blockOf (u i)) = F i := S.family_eq_of_mem_families hFm hbu
      obtain ⟨he1, hodd⟩ := S.om_lev1 hou
      obtain ⟨cr, wt, h1, h2, h3, h4, h5, h6⟩ := S.fam_unit ha0 hD1 hDa Z he1 hodd (by rw [hfe]; exact hbv)
        (S.om_lev1 hov).1 (by rw [hfe]; exact hmid)
      exact ⟨cr, wt, fun _ _ => ⟨h1, h2, h3, h4, by rw [← hfe]; exact h5, h6⟩⟩
    · exact ⟨⟨0, fun _ => G.blockOf (u i), fun _ => [], fun _ => none⟩, .on 0 (G.blockOf (u i)) [],
        fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose CR WT hunit using hunitE
  -- the bottom end
  obtain ⟨b0, ms0, bf, hb0row, hfrag0, hhead0, hlast0, hbf, hσ0, hown0, hF0⟩ :
      ∃ (b0 : G.Block) (ms0 : List G.Move) (bf : Bool), b0.2.val ≤ hs a1 ∧
        S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) b0 ms0 ∧
        (∀ mv ∈ ms0.head?, ¬ mv.isLeaf) ∧ (∀ mv ∈ ms0.getLast?, ¬ mv.isLink) ∧
        (bf = false → ms0 = [] ∧ b0.2.val = 0) ∧
        G.blockDist (G.blockOf (v 0)) (S3Geom.endBlock b0 ms0) ≤ G.D - 1 ∧
        (∀ mv ∈ ms0, mv.blk ∈ famOf x) ∧
        (bf = true → x = .inr (.inr (famOf x)) ∧ famOf x ∈ S.families a0 a1 E) := by
    have hv0 := hadjV 0 (Nat.zero_le _)
    rw [hp0, hx0] at hv0
    rcases hx with hxb | hxF
    · -- the sub-path starts at `b₁`: the first check lies on row 0
      subst hxb
      obtain ⟨x', hx', -⟩ : ∃ x', v 0 = (x', 0) ∧ S.ctop a0 a1 Z E (.bot x') ≠ 0 := by
        rcases hv0 with h | h
        · simp [gadj0] at h
        · exact h
      have hrow : (G.blockOf (v 0)).2.val = 0 := by
        rw [hx']
        simp [S3Geom.blockOf, S3Geom.brow]
      refine ⟨G.blockOf (v 0), [], false, by omega, ⟨trivial, List.isChain_nil,
        fun mv hmv => absurd hmv (by simp), List.Pairwise.nil⟩, fun mv hmv => absurd hmv (by simp),
        fun mv hmv => absurd hmv (by simp), fun _ => ⟨rfl, hrow⟩, ?_, fun mv hmv => absurd hmv (by simp),
        fun h => absurd h (by simp)⟩
      show G.blockDist (G.blockOf (v 0)) (G.blockOf (v 0)) ≤ G.D - 1
      rw [G.blockDist_self]
      exact Nat.zero_le _
    · -- the sub-path starts at a bottom-strip family
      obtain ⟨F0, rfl⟩ : ∃ F0, x = .inr (.inr F0) := by
        rcases x with u' | b | F'
        · exact hxF.elim
        · exact hxF.elim
        · exact ⟨F', rfl⟩
      obtain ⟨hF0, c1, hc1, hr1⟩ := hxF
      obtain ⟨-, hbv, -⟩ := S.gadj_fam_check hv0
      have hfe : S.family a0 a1 E c1 = F0 := S.family_eq_of_mem_families hF0 hc1
      obtain ⟨b, σ, ms, h1, -, h3, h4, h5, h6, h7, -, h9⟩ := S.bot_route ha0 hD1 hDa hT1
        (S.badD_of_mem_family (show c1 ∈ S.family a0 a1 E c1 by rw [hfe]; exact hc1)) hr1
        (show G.blockOf (v 0) ∈ S.family a0 a1 E c1 by rw [hfe]; exact hbv)
      refine ⟨b, ms, true, h1, h3, h4, h5, fun h => absurd h (by simp), by rw [h7]; exact h9,
        fun mv hmv => by rw [← hfe]; exact h6 mv hmv, fun _ => ⟨rfl, hF0⟩⟩
  -- the top end
  obtain ⟨mst, tf, het1, hfragT, hheadT, hsepT, hendT, htf, hemp, hownT, hFT⟩ :
      ∃ (mst : List G.Move) (tf : Bool), (tf = true → hs a1 + 1 ≤ (G.blockOf (u (m + 1))).2.val) ∧
        S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) (G.blockOf (u (m + 1))) mst ∧
        (∀ mv ∈ mst.head?, ¬ mv.isLeaf) ∧ (∀ mv ∈ mst, G.D ≤ G.blockDist (G.blockOf (u (m + 1))) mv.blk) ∧
        G.ny ≤ (S3Geom.endBlock (G.blockOf (u (m + 1))) mst).2.val + 1 + hs a1 + (G.D - 1 + a1) ∧
        (tf = false → mst = [] ∧ (G.blockOf (u (m + 1))).2.val + 1 = G.ny) ∧
        (G.ny ≤ (G.blockOf (u (m + 1))).2.val + 1 + hs a1 → mst = []) ∧
        (∀ mv ∈ mst, mv.blk ∈ famOf y) ∧
        (tf = true → y = .inr (.inr (famOf y)) ∧ famOf y ∈ S.families a0 a1 E ∧
          G.blockOf (u (m + 1)) ∈ famOf y ∧ G.blockOf (u (m + 1)) ∈ S.lev1 a0 E) := by
    have hu' := hadjU (m + 1) (by omega) le_rfl
    rw [hpl, hyl] at hu'
    rcases hy with hyb | hyF
    · -- the sub-path ends at `b₂`: the last check lies on the top row
      subst hyb
      obtain ⟨x', hx', -⟩ : ∃ x', u (m + 1) = (x', Fin.last _) ∧ S.ctop a0 a1 Z E (.top x') ≠ 0 := by
        rcases hu' with h | h
        · exact h
        · simp [gadj0] at h
      have hrow : (G.blockOf (u (m + 1))).2.val + 1 = G.ny := by
        have h1 := top_row (G := G) x'
        have h2 := (G.blockOf (u (m + 1))).2.isLt
        rw [hx'] at h2 ⊢
        omega
      refine ⟨[], false, fun h => absurd h (by simp), ⟨trivial, List.isChain_nil,
        fun mv hmv => absurd hmv (by simp), List.Pairwise.nil⟩, fun mv hmv => absurd hmv (by simp),
        fun mv hmv => absurd hmv (by simp), ?_, fun _ => ⟨rfl, hrow⟩, fun _ => rfl,
        fun mv hmv => absurd hmv (by simp), fun h => absurd h (by simp)⟩
      show G.ny ≤ (G.blockOf (u (m + 1))).2.val + 1 + hs a1 + (G.D - 1 + a1)
      omega
    · obtain ⟨Fy, rfl⟩ : ∃ Fy, y = .inr (.inr Fy) := by
        rcases y with u' | b | F'
        · exact hyF.elim
        · exact hyF.elim
        · exact ⟨F', rfl⟩
      obtain ⟨hFy, c2, hc2, hr2⟩ := hyF
      obtain ⟨-, hbu, hou⟩ := S.gadj_check_fam hu'
      have hfe : S.family a0 a1 E (G.blockOf (u (m + 1))) = Fy := S.family_eq_of_mem_families hFy hbu
      obtain ⟨ms, h1, h2, h3, h4, h5, h6, h7⟩ := S.top_route ha0 hD1 hDa ha01 hT1 (S.om_lev1 hou).1
        (show c2 ∈ S.family a0 a1 E (G.blockOf (u (m + 1))) by rw [hfe]; exact hc2) hr2
      exact ⟨ms, true, fun _ => h1, h3, h4, h5, h7, fun h => absurd h (by simp), h2,
        fun mv hmv => by rw [← hfe]; exact h6 mv hmv, fun _ => ⟨rfl, hFy, hbu, (S.om_lev1 hou).1⟩⟩
  -- the skeleton
  set fams : List (G.CRoute × G.Wit) := (List.range m).map (fun i => (CR (i + 1), WT (i + 1))) with hfams
  set σ : ℕ → G.Block := fun i => if i = 0 then S3Geom.endBlock b0 ms0 else (CR i).last with hσdef
  have hσ0' : σ 0 = S3Geom.endBlock b0 ms0 := by
    rw [hσdef]
    simp
  have hσi : ∀ i, 1 ≤ i → σ i = (CR i).last := by
    intro i hi
    rw [hσdef]
    simp [show i ≠ 0 by omega]
  have hσv : ∀ i ≤ m, G.blockDist (G.blockOf (v i)) (σ i) ≤ G.D - 1 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      rw [hσ0']
      exact hσ0
    · rw [hσi i h]
      exact (hunit i h hi).2.2.2.1
  let sk : G.T2Sk := ⟨b0, ms0, bf, fams, G.blockOf (u (m + 1)), mst, tf⟩
  have hlenf : fams.length = m := by simp [hfams]
  have hjumps : sk.jumps = (List.range (m + 1)).map (fun i => (σ i, G.blockOf (u (i + 1)))) := by
    have hc : sk.covers = (List.range (m + 1)).map σ := by
      show S3Geom.endBlock b0 ms0 :: fams.map (fun f => f.1.last) = _
      rw [List.range_succ_eq_map, List.map_cons, hσ0']
      congr 1
      simp only [hfams, List.map_map]
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, Nat.succ_eq_add_one]
      rw [hσi (i + 1) (by omega)]
    have hr : sk.roots = (List.range (m + 1)).map (fun i => G.blockOf (u (i + 1))) := by
      show fams.map (fun f => f.1.r 0) ++ [G.blockOf (u (m + 1))] = _
      rw [List.range_succ, List.map_append, List.map_singleton]
      congr 1
      simp only [hfams, List.map_map]
      refine List.map_congr_left fun i hi => ?_
      have hi' := List.mem_range.1 hi
      exact (hunit (i + 1) (by omega) (by omega)).2.2.1
    show sk.covers.zip sk.roots = _
    rw [hc, hr, List.zip_map']
  have hjlen : sk.jumps.length = m + 1 := by
    rw [hjumps]
    simp
  have hjget : ∀ i (hi : i < sk.jumps.length), sk.jumps[i] = (σ i, G.blockOf (u (i + 1))) := by
    intro i hi
    rw [List.getElem_of_eq hjumps hi]
    simp
  -- property (R) on the jumps between two families
  have hfnode : ∀ i ≤ m + 1, (i = 0 → bf = true) → (i = m + 1 → tf = true) →
      ∃ Fm, nd l (p i) = .inr (.inr Fm) := by
    intro i hi h0 hL
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      rw [hp0, hx0]
      exact ⟨famOf x, (hF0 (h0 rfl)).1⟩
    · rcases eq_or_lt_of_le hi with h' | h'
      · subst h'
        rw [hpl, hyl]
        exact ⟨famOf y, (hFT (hL rfl)).1⟩
      · exact ⟨F i, hF i h (by omega)⟩
  have hR : ∀ i (hi : i < sk.jumps.length), (sk.bf = true ∨ i ≠ 0) → (sk.tf = true ∨ i + 1 ≠ sk.jumps.length) →
      a1 + 2 - G.D ≤ G.blockDist (sk.jumps[i]).1 (sk.jumps[i]).2 := by
    intro i hi hb ht
    rw [hjget i hi]
    rw [hjlen] at hi ht
    obtain ⟨Fa, hFa⟩ := hfnode i (by omega) (fun h => hb.resolve_right (fun h' => h' h))
      (fun h => absurd h (by omega))
    obtain ⟨Fb, hFb⟩ := hfnode (i + 1) (by omega) (fun h => absurd h (by omega))
      (fun h => ht.resolve_right (fun h' => h' h))
    have hpi := hp i (i + 1) (by omega) (by omega)
    have hmid : ∀ k, p i < k → k < p (i + 1) → ∀ Fc, l[k]? ≠ some (.inr (.inr Fc)) := by
      intro k hk1 hk2 Fc hc
      refine hnofam k (fun j hj hkj => ?_) ⟨Fc, nd_of_getElem? hc⟩
      subst hkj
      by_cases hji : j ≤ i
      · have := hpmono j i hji (by omega)
        omega
      · have := hpmono (i + 1) j (by omega) hj
        omega
    obtain ⟨u', v', hu', hv', hfar⟩ := S.path_R hhd hlst hnd hch hbd hpi
      (by rw [← hFa]; exact getElem?_nd (hplt i (by omega)))
      (by rw [← hFb]; exact getElem?_nd (hplt (i + 1) (by omega))) hmid
    have e1 : u' = v i := by
      have h1 := getElem?_nd (l := l) (p := p i + 1)
        (by have := hgap i (by omega); have := hplt (i + 1) (by omega); omega)
      rw [hv i (by omega)] at h1
      rw [h1] at hu'
      simpa using hu'.symm
    have e2 : v' = u (i + 1) := by
      have h1 := getElem?_nd (l := l) (p := p (i + 1) - 1) (by have := hplt (i + 1) (by omega); omega)
      rw [hu (i + 1) (by omega) (by omega)] at h1
      rw [h1] at hv'
      simpa using hv'.symm
    rw [e1, e2] at hfar
    have t := G.blockDist_triangle (G.blockOf (v i)) (σ i) (G.blockOf (u (i + 1)))
    have t2 := hσv i (by omega)
    show a1 + 2 - G.D ≤ G.blockDist (σ i) (G.blockOf (u (i + 1)))
    omega
  -- the exchange inequality (X) in block units
  have hX : (((sk.jumps.map fun q => S3Geom.bl1 q.1 q.2).sum : ℕ) : ℝ) ≤
      wmax / wmin * (((sk.fams.map fun f => S3Geom.bl1 (f.1.r 0) f.1.last).sum : ℕ) : ℝ) +
        2 * G.D * (sk.fams.length + 1) + 2 * G.D * (wmax / wmin) * sk.fams.length +
        wmax / wmin * (((S3Geom.endBlock sk.b0 sk.ms0).2.val : ℝ) + G.D) +
        wmax / wmin * ((G.ny : ℝ) - sk.et.2.val) + 2 * wh / (wmin * G.L) := by
    have hJs : (sk.jumps.map fun q => S3Geom.bl1 q.1 q.2).sum =
        ∑ i ∈ Finset.range (m + 1), S3Geom.bl1 (σ i) (G.blockOf (u (i + 1))) := by
      rw [hjumps, List.map_map, sum_map_range]
      rfl
    have hFs : (sk.fams.map fun f => S3Geom.bl1 (f.1.r 0) f.1.last).sum =
        ∑ i ∈ Finset.range m, S3Geom.bl1 (G.blockOf (u (i + 1))) (σ (i + 1)) := by
      show (fams.map fun f => S3Geom.bl1 (f.1.r 0) f.1.last).sum = _
      simp only [hfams, List.map_map]
      rw [sum_map_range]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have hr0 := (hunit (i + 1) (by omega) (by omega)).2.2.1
      simp only [Function.comp_apply]
      rw [hr0, hσi (i + 1) (by omega)]
    have hlen' : sk.fams.length = m := hlenf
    have hb0' : S3Geom.endBlock sk.b0 sk.ms0 = σ 0 := hσ0'.symm
    rw [hJs, hFs, hlen', hb0', Nat.cast_sum, Nat.cast_sum]
    have hA : ∑ i ∈ Finset.range (m + 1), (S3Geom.bl1 (σ i) (G.blockOf (u (i + 1))) : ℝ) ≤
        ∑ i ∈ Finset.range (m + 1), (S3Geom.blockL1 (v i) (u (i + 1)) : ℝ) + (m + 1) * (2 * ((G.D : ℝ) - 1)) := by
      have hterm : ∀ i ∈ Finset.range (m + 1), (S3Geom.bl1 (σ i) (G.blockOf (u (i + 1))) : ℝ) ≤
          (S3Geom.blockL1 (v i) (u (i + 1)) : ℝ) + 2 * ((G.D : ℝ) - 1) := by
        intro i hi
        have hi' := Finset.mem_range.1 hi
        have t1 := bl1_triangle (σ i) (G.blockOf (v i)) (G.blockOf (u (i + 1)))
        have t2 := bl1_le_blockDist (σ i) (G.blockOf (v i))
        have t3 := hσv i (by omega)
        rw [G.blockDist_comm] at t3
        have e : S3Geom.bl1 (G.blockOf (v i)) (G.blockOf (u (i + 1))) = S3Geom.blockL1 (v i) (u (i + 1)) := rfl
        have hn : S3Geom.bl1 (σ i) (G.blockOf (u (i + 1))) + 2 ≤ S3Geom.blockL1 (v i) (u (i + 1)) + 2 * G.D := by
          omega
        have hn' : ((S3Geom.bl1 (σ i) (G.blockOf (u (i + 1))) + 2 : ℕ) : ℝ) ≤
            ((S3Geom.blockL1 (v i) (u (i + 1)) + 2 * G.D : ℕ) : ℝ) := by
          exact_mod_cast hn
        push_cast at hn'
        linarith
      calc ∑ i ∈ Finset.range (m + 1), (S3Geom.bl1 (σ i) (G.blockOf (u (i + 1))) : ℝ)
          ≤ ∑ i ∈ Finset.range (m + 1), ((S3Geom.blockL1 (v i) (u (i + 1)) : ℝ) + 2 * ((G.D : ℝ) - 1)) :=
            Finset.sum_le_sum hterm
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hB : ∑ i ∈ Finset.range m, (S3Geom.blockL1 (u (i + 1)) (v (i + 1)) : ℝ) ≤
        ∑ i ∈ Finset.range m, (S3Geom.bl1 (G.blockOf (u (i + 1))) (σ (i + 1)) : ℝ) + m * (2 * ((G.D : ℝ) - 1)) := by
      have hterm : ∀ i ∈ Finset.range m, (S3Geom.blockL1 (u (i + 1)) (v (i + 1)) : ℝ) ≤
          (S3Geom.bl1 (G.blockOf (u (i + 1))) (σ (i + 1)) : ℝ) + 2 * ((G.D : ℝ) - 1) := by
        intro i hi
        have hi' := Finset.mem_range.1 hi
        have t1 := bl1_triangle (G.blockOf (u (i + 1))) (σ (i + 1)) (G.blockOf (v (i + 1)))
        have t2 := bl1_le_blockDist (σ (i + 1)) (G.blockOf (v (i + 1)))
        have t3 := hσv (i + 1) (by omega)
        rw [G.blockDist_comm] at t3
        have e : S3Geom.bl1 (G.blockOf (u (i + 1))) (G.blockOf (v (i + 1))) =
            S3Geom.blockL1 (u (i + 1)) (v (i + 1)) := rfl
        have hn : S3Geom.blockL1 (u (i + 1)) (v (i + 1)) + 2 ≤
            S3Geom.bl1 (G.blockOf (u (i + 1))) (σ (i + 1)) + 2 * G.D := by
          omega
        have hn' : ((S3Geom.blockL1 (u (i + 1)) (v (i + 1)) + 2 : ℕ) : ℝ) ≤
            ((S3Geom.bl1 (G.blockOf (u (i + 1))) (σ (i + 1)) + 2 * G.D : ℕ) : ℝ) := by
          exact_mod_cast hn
        push_cast at hn'
        linarith
      calc ∑ i ∈ Finset.range m, (S3Geom.blockL1 (u (i + 1)) (v (i + 1)) : ℝ)
          ≤ ∑ i ∈ Finset.range m, ((S3Geom.bl1 (G.blockOf (u (i + 1))) (σ (i + 1)) : ℝ) + 2 * ((G.D : ℝ) - 1)) :=
            Finset.sum_le_sum hterm
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hvy : ((v 0).2.val : ℝ) ≤ G.L * (((σ 0).2.val : ℝ) + G.D) := by
      have h1 := Nat.lt_mul_div_succ (v 0).2.val G.hL
      have h2 : (G.blockOf (v 0)).2.val = (v 0).2.val / G.L := rfl
      have h3 := hσv 0 (Nat.zero_le _)
      have h4 : ndist (G.blockOf (v 0)).2.val (σ 0).2.val ≤ G.blockDist (G.blockOf (v 0)) (σ 0) :=
        le_max_right _ _
      have h5 : (G.blockOf (v 0)).2.val + 1 ≤ (σ 0).2.val + G.D := by
        simp only [ndist] at h4
        omega
      rw [h2] at h5
      have h6 := Nat.mul_le_mul_left G.L h5
      have h7 : (v 0).2.val ≤ G.L * ((σ 0).2.val + G.D) := (lt_of_lt_of_le h1 h6).le
      exact_mod_cast h7
    have hhy : ((G.h - (u (m + 1)).2.val : ℕ) : ℝ) ≤ G.L * ((G.ny : ℝ) - (G.blockOf (u (m + 1))).2.val) := by
      have h1 : (G.blockOf (u (m + 1))).2.val = (u (m + 1)).2.val / G.L := rfl
      have h2 : G.L * ((u (m + 1)).2.val / G.L) ≤ (u (m + 1)).2.val := Nat.mul_div_le _ _
      have h3 := G.h_succ
      have h4 := (u (m + 1)).2.isLt
      have h2' : (G.L : ℝ) * (((u (m + 1)).2.val / G.L : ℕ) : ℝ) ≤ ((u (m + 1)).2.val : ℝ) := by
        exact_mod_cast h2
      have h3' : (G.h : ℝ) + 1 = G.ny * G.L := by exact_mod_cast h3
      rw [Nat.cast_sub (by omega : (u (m + 1)).2.val ≤ G.h), h1]
      linarith
    have hmet' := hmet
    rw [show ((2 * (G.L - 1) : ℕ) : ℝ) = 2 * ((G.L : ℝ) - 1) by push_cast [Nat.cast_sub G.hL]; ring] at hmet'
    exact metric_convert G.hL hmin0 hmax0 hA hB hvy hhy hmet'
  -- the counted blocks: bad (convention (i)), in the sampled rows
  have hfamB : ∀ {Fm : Set G.Block}, Fm ∈ S.families a0 a1 E → ∀ b ∈ Fm, S.badD E b := by
    intro Fm hFm b hb
    obtain ⟨c0, hc0, rfl⟩ := (S.mem_families).1 hFm
    exact S.badD_of_mem_family hb
  have hrowsF : ∀ i, 1 ≤ i → i ≤ m → ∀ b ∈ (CR i).blocks ++ (WT i).blocks,
      S.badD E b ∧ hs a1 + 1 ≤ b.2.val ∧ b.2.val + 2 + hs a1 ≤ G.ny := by
    intro i hi1 hi b hb
    obtain ⟨hFm, -, -, -, -, hmid⟩ := hst i hi1 hi
    have hbF := (hunit i hi1 hi).2.2.2.2.1 b hb
    have := hmid b hbF
    exact ⟨hfamB hFm b hbF, by omega, by omega⟩
  have hLt : ∀ b ∈ (if tf then [G.blockOf (u (m + 1))] else []) ++ mst.map S3Geom.Move.blk,
      tf = true ∧ b ∈ famOf y := by
    intro b hb
    cases htfv : tf
    · obtain ⟨hm0, -⟩ := htf htfv
      rw [htfv, hm0] at hb
      simp at hb
    · refine ⟨rfl, ?_⟩
      rw [htfv] at hb
      rcases List.mem_append.1 hb with hb | hb
      · simp only [↓reduceIte, List.mem_singleton] at hb
        rw [hb]
        exact (hFT htfv).2.2.1
      · obtain ⟨mv, hmv, rfl⟩ := List.mem_map.1 hb
        exact hownT mv hmv
  have hcnt : ∀ b ∈ sk.counted, S.badD E b ∧ 2 ≤ b.2.val ∧ b.2.val + 3 ≤ G.ny := by
    intro b hb
    have hb' : b ∈ ms0.map S3Geom.Move.blk ++ (fams.flatMap (fun f => f.1.blocks ++ f.2.blocks) ++
        ((if tf then [G.blockOf (u (m + 1))] else []) ++ mst.map S3Geom.Move.blk)) := hb
    rcases List.mem_append.1 hb' with hb | hb
    · obtain ⟨mv, hmv, rfl⟩ := List.mem_map.1 hb
      obtain ⟨h1, h2, h3⟩ := hfrag0.2.2.1 mv hmv
      exact ⟨h3, by omega, by omega⟩
    rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨f, hf, hbf'⟩ := List.mem_flatMap.1 hb
      have hf' : f ∈ (List.range m).map (fun i => (CR (i + 1), WT (i + 1))) := hf
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf'
      have hi' := List.mem_range.1 hi
      obtain ⟨h1, h2, h3⟩ := hrowsF (i + 1) (by omega) (by omega) b hbf'
      exact ⟨h1, by omega, by omega⟩
    rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨htfv, -⟩ := hLt b (List.mem_append_left _ hb)
      rw [htfv] at hb
      simp only [↓reduceIte, List.mem_singleton] at hb
      subst hb
      obtain ⟨-, -, -, hlev⟩ := hFT htfv
      obtain ⟨h1, h2⟩ := S.lev1_rows (by omega) hlev
      exact ⟨S.badD_of_lev1 hlev, h1, h2⟩
    · obtain ⟨mv, hmv, rfl⟩ := List.mem_map.1 hb
      obtain ⟨h1, h2, h3⟩ := hfragT.2.2.1 mv hmv
      exact ⟨h3, by omega, by omega⟩
  -- the counted blocks are pairwise at least `D` apart: within a family, and blocks of distinct families
  have hdistF : ∀ i j, i < j → j ≤ m + 1 → ∀ Fa Fb, nd l (p i) = .inr (.inr Fa) →
      nd l (p j) = .inr (.inr Fb) → Fa ≠ Fb := by
    intro i j hij hj Fa Fb ha hb' hab
    subst hab
    have := (nd_eq_iff hnd (hplt i (by omega)) (hplt j hj)).1 (ha.trans hb'.symm)
    have := hp i j hij hj
    omega
  have hL0 : ∀ b ∈ ms0.map S3Geom.Move.blk, bf = true ∧ b ∈ famOf x := by
    intro b hb
    obtain ⟨mv, hmv, rfl⟩ := List.mem_map.1 hb
    cases hbfv : bf
    · rw [(hbf hbfv).1] at hmv
      simp at hmv
    · exact ⟨rfl, hown0 mv hmv⟩
  have hLf : ∀ b ∈ fams.flatMap (fun f => f.1.blocks ++ f.2.blocks), ∃ i, 1 ≤ i ∧ i ≤ m ∧ b ∈ F i := by
    intro b hb
    obtain ⟨f, hf, hbf'⟩ := List.mem_flatMap.1 hb
    have hf' : f ∈ (List.range m).map (fun i => (CR (i + 1), WT (i + 1))) := hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf'
    have hi' := List.mem_range.1 hi
    exact ⟨i + 1, by omega, by omega, (hunit (i + 1) (by omega) (by omega)).2.2.2.2.1 b hbf'⟩
  have hpwc : sk.counted.Pairwise (fun b b' => G.D ≤ G.blockDist b b') := by
    show (ms0.map S3Geom.Move.blk ++ (fams.flatMap (fun f => f.1.blocks ++ f.2.blocks) ++
      ((if tf then [G.blockOf (u (m + 1))] else []) ++ mst.map S3Geom.Move.blk))).Pairwise _
    refine List.pairwise_append.2 ⟨hfrag0.2.2.2, List.pairwise_append.2 ⟨?_, ?_, ?_⟩, ?_⟩
    · -- the families
      refine List.pairwise_flatMap.2 ⟨fun f hf => ?_, ?_⟩
      · have hf' : f ∈ (List.range m).map (fun i => (CR (i + 1), WT (i + 1))) := hf
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf'
        have hi' := List.mem_range.1 hi
        exact (hunit (i + 1) (by omega) (by omega)).2.2.2.2.2
      · show ((List.range m).map (fun i => (CR (i + 1), WT (i + 1)))).Pairwise _
        rw [List.pairwise_map]
        refine List.pairwise_lt_range.imp_of_mem fun {i j} hi hj hij b hb b' hb' => ?_
        have hi' := List.mem_range.1 hi
        have hj' := List.mem_range.1 hj
        exact S.sep_of_fam_ne hDa (hst (i + 1) (by omega) (by omega)).1 (hst (j + 1) (by omega) (by omega)).1
          (hdistF (i + 1) (j + 1) (by omega) (by omega) _ _ (hF (i + 1) (by omega) (by omega))
            (hF (j + 1) (by omega) (by omega)))
          ((hunit (i + 1) (by omega) (by omega)).2.2.2.2.1 b hb)
          ((hunit (j + 1) (by omega) (by omega)).2.2.2.2.1 b' hb')
    · -- the top end
      refine List.pairwise_append.2 ⟨?_, hfragT.2.2.2, ?_⟩
      · split_ifs <;> simp
      · intro b hb b' hb'
        cases htfv : tf
        · rw [htfv] at hb
          simp at hb
        · rw [htfv] at hb
          simp only [↓reduceIte, List.mem_singleton] at hb
          subst hb
          obtain ⟨mv, hmv, rfl⟩ := List.mem_map.1 hb'
          exact hsepT mv hmv
    · -- the families against the top end
      intro b hb b' hb'
      obtain ⟨i, hi1, hi, hbF⟩ := hLf b hb
      obtain ⟨htf', hb'F⟩ := hLt b' hb'
      obtain ⟨hyn, hFy, -, -⟩ := hFT htf'
      exact S.sep_of_fam_ne hDa (hst i hi1 hi).1 hFy
        (hdistF i (m + 1) (by omega) le_rfl _ _ (hF i hi1 hi) (by rw [hpl, hyl]; exact hyn)) hbF hb'F
    · -- the bottom end against the rest
      intro b hb b' hb'
      obtain ⟨hbf', hbF0⟩ := hL0 b hb
      obtain ⟨hxn, hF0m⟩ := hF0 hbf'
      rcases List.mem_append.1 hb' with hb' | hb'
      · obtain ⟨i, hi1, hi, hb'F⟩ := hLf b' hb'
        exact S.sep_of_fam_ne hDa hF0m (hst i hi1 hi).1
          (hdistF 0 i (by omega) (by omega) _ _ (by rw [hp0, hx0]; exact hxn) (hF i hi1 hi)) hbF0 hb'F
      · obtain ⟨htf', hb'F⟩ := hLt b' hb'
        obtain ⟨hyn, hFy, -, -⟩ := hFT htf'
        exact S.sep_of_fam_ne hDa hF0m hFy
          (hdistF 0 (m + 1) (by omega) le_rfl _ _ (by rw [hp0, hx0]; exact hxn) (by rw [hpl, hyl]; exact hyn))
          hbF0 hb'F
  refine ⟨sk, ⟨⟨hb0row, hfrag0.1, hfrag0.2.1, hhead0, hlast0,
    fun mv hmv => ⟨(hfrag0.2.2.1 mv hmv).1, (hfrag0.2.2.1 mv hmv).2.1⟩, hbf⟩, fun f hf => ?_,
    ⟨het1, hfragT.1, hfragT.2.1, hheadT, fun mv hmv => ⟨(hfragT.2.2.1 mv hmv).1, (hfragT.2.2.1 mv hmv).2.1⟩,
      hemp, hendT, htf⟩, hR, hX, fun b hb => ⟨(hcnt b hb).2.1, (hcnt b hb).2.2⟩, hpwc⟩, fun c hc => ?_⟩
  · have hf' : f ∈ (List.range m).map (fun i => (CR (i + 1), WT (i + 1))) := hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf'
    have hi' := List.mem_range.1 hi
    obtain ⟨h1, h2, -⟩ := hunit (i + 1) (by omega) (by omega)
    exact ⟨h1, h2, fun b hb => ⟨(hrowsF (i + 1) (by omega) (by omega) b hb).2.1,
      (hrowsF (i + 1) (by omega) (by omega) b hb).2.2⟩⟩
  · obtain ⟨hbad, h1, h2⟩ := hcnt c hc
    exact S.bad_of_badD_sampled hbad h1 h2

end Stage1

namespace S3Fam

variable (fam : S3Fam)

/-- **T2SkelExists is a theorem** whenever `a0 ≥ 2`, `a0 ≤ a1`, `D = 4 + ⌊2R/L⌋ ≤ a0 + 1`, and the solvers' weights
are nonnegative, in `[wmin, wmax]` on bulk edges (`wmin > 0`) and at most `wh` on half-edges. -/
theorem t2SkelExists {a0 a1 : ℕ} (K : BoundConsts) (ha0 : 2 ≤ a0) (hD : 4 + 2 * fam.R / fam.L ≤ a0 + 1)
    (ha01 : a0 ≤ a1) (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny))
    {wmin wmax wh : ℝ} (hmin0 : 0 < wmin) (hmax0 : 0 ≤ wmax) (hwh0 : 0 ≤ wh)
    (hwt0 : ∀ nx ny hnx hny e, 0 ≤ (Z nx ny hnx hny).wt e)
    (hmin : ∀ nx ny hnx hny e, S3Geom.isBulk e → wmin ≤ (Z nx ny hnx hny).wt e)
    (hmax : ∀ nx ny hnx hny e, S3Geom.isBulk e → (Z nx ny hnx hny).wt e ≤ wmax)
    (hbot : ∀ nx ny hnx hny x, (Z nx ny hnx hny).wt (.bot x) ≤ wh)
    (htop : ∀ nx ny hnx hny x, (Z nx ny hnx hny).wt (.top x) ≤ wh) :
    fam.T2SkelExists a0 a1 Z (wmax / wmin) (2 * wh / (wmin * fam.L)) K :=
  fun nx ny _ _ hny1 => (fam.stage1 nx ny (by omega) hny1).t2SkelExistsOn ha0
    (show 1 ≤ 4 + 2 * fam.R / fam.L from le_add_right (by norm_num)) hD ha01 _ (hwt0 _ _ _ _) hmin0 hmax0 hwh0
    (hmin _ _ _ _) (hmax _ _ _ _) (hbot _ _ _ _) (htop _ _ _ _)

/-- **The T2 term from the counting hypothesis**: with the weight bounds of `t2SkelExists`,
`H2D_T2count ⟹ H2D_T2ev` (metric ratio `wmax / wmin`, boundary constant `2 wh / (wmin L)`). -/
theorem h2dT2ev_of_T2count {a0 a1 : ℕ} (K : BoundConsts) (ha0 : 2 ≤ a0) (hD : 4 + 2 * fam.R / fam.L ≤ a0 + 1)
    (ha01 : a0 ≤ a1) (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny))
    {wmin wmax wh : ℝ} (hmin0 : 0 < wmin) (hmax0 : 0 ≤ wmax) (hwh0 : 0 ≤ wh)
    (hwt0 : ∀ nx ny hnx hny e, 0 ≤ (Z nx ny hnx hny).wt e)
    (hmin : ∀ nx ny hnx hny e, S3Geom.isBulk e → wmin ≤ (Z nx ny hnx hny).wt e)
    (hmax : ∀ nx ny hnx hny e, S3Geom.isBulk e → (Z nx ny hnx hny).wt e ≤ wmax)
    (hbot : ∀ nx ny hnx hny x, (Z nx ny hnx hny).wt (.bot x) ≤ wh)
    (htop : ∀ nx ny hnx hny x, (Z nx ny hnx hny).wt (.top x) ≤ wh) {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hcount : fam.H2D_T2count a0 a1 (wmax / wmin) (2 * wh / (wmin * fam.L)) K ε) :
    fam.H2D_T2ev a0 a1 Z K q ε :=
  fam.h2dT2ev_of_count a0 a1 Z _ _ K hq0 hq1
    (fam.t2SkelExists K ha0 hD ha01 Z hmin0 hmax0 hwh0 hwt0 hmin hmax hbot htop) hcount

end S3Fam

end QECML
