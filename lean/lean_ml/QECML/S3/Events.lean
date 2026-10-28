import QECML.S3.Geometry

/-!
# Admissible stage-1 rules, block events, locality and the per-block hypothesis (H)

* `Stage1 G`: for each block `c` a map `F c` from syndromes to edge sets with (R1) locality
  (it depends only on the syndrome in the window `W_c`) and ownership (it returns only edges owned by `c`). (R3)
  determinism holds for every Lean function; the consequence of (R2) covariance that the certificate uses is the
  named hypothesis `Htype` (module `QECML.S3.Hypotheses`).
* `C0`, `resid` (`D' = D + ∂C_0`), `Fcfg` (`F = E + C_0`), `flagged`, `long`, `bad`: block `c` is
  bad if `D'` meets it, or if a path of `F` inside `N_1(c)` joins a check of `c` to a check at `ℓ∞` distance at
  least `L` from `c`.
* `bad_local` (locality): `bad E c` depends only on `E` on `Nbhd c`, the edges with an endpoint in a window of a
  block of `N_1(c)`.
* `hypH_of_block_bound`: per-block bounds `P(bad c) ≤ ε` on the sampled rows give Hypothesis (H):
  `P(all of T bad) ≤ ε^{|T|}` for every set `T` of sampled blocks at pairwise block distance at least `D`.
-/

open Finset

namespace QECML

/-- An admissible stage-1 rule ((R1) locality and ownership). -/
structure Stage1 (G : S3Geom) where
  /-- the owned output of block `c` on the syndrome `D` -/
  F : G.Block → (G.V → ZMod 2) → (G.Ed → ZMod 2)
  /-- (R1) locality: `F c` reads the syndrome only in the window of `c` -/
  loc : ∀ c D D', (∀ v, G.inWin c v → D v = D' v) → F c D = F c D'
  /-- ownership: `F c` returns only edges owned by `c` -/
  own : ∀ c D e, G.owner e ≠ c → F c D e = 0

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- The syndrome of an error configuration. -/
abbrev syn (E : G.Ed → ZMod 2) : G.V → ZMod 2 := psyn G.w G.h E

/-- `C_0`: the sum of the owned outputs of all blocks. -/
def C0 (D : G.V → ZMod 2) : G.Ed → ZMod 2 := ∑ c, S.F c D

/-- The residual syndrome `D' = D + ∂C_0`. -/
def resid (E : G.Ed → ZMod 2) : G.V → ZMod 2 := syn E + psyn G.w G.h (S.C0 (syn E))

/-- `F = E + C_0`; its odd vertices are the residual. -/
def Fcfg (E : G.Ed → ZMod 2) : G.Ed → ZMod 2 := E + S.C0 (syn E)

/-- Block `c` is flagged if the residual meets it. -/
def flagged (E : G.Ed → ZMod 2) (c : G.Block) : Prop := ∃ v, G.blockOf v = c ∧ S.resid E v ≠ 0

/-- One step of a path of `F` inside `N_1(c)` (bulk edges only). -/
def stepIn (E : G.Ed → ZMod 2) (c : G.Block) (a b : G.V) : Prop :=
  G.blockDist (G.blockOf a) c ≤ 1 ∧ G.blockDist (G.blockOf b) c ≤ 1 ∧
    ∃ e : G.Ed, e.ends = {a, b} ∧ a ≠ b ∧ S.Fcfg E e ≠ 0

/-- Block `c` is long if a path of `F` inside `N_1(c)` joins a check of `c` to a check at distance `≥ L`. -/
def long (E : G.Ed → ZMod 2) (c : G.Block) : Prop :=
  ∃ a b, G.blockOf a = c ∧ G.L ≤ G.distVB b c ∧ Relation.ReflTransGen (S.stepIn E c) a b

/-- The bad event of block `c` (flagged or long). Convention (i), rough rows bad by fiat, is applied in the 2D lemma,
whose Hypothesis (H) concerns the sampled rows only. -/
def bad (E : G.Ed → ZMod 2) (c : G.Block) : Prop := S.flagged E c ∨ S.long E c

/-! ## Locality -/

theorem C0_apply (D : G.V → ZMod 2) (e : G.Ed) : S.C0 D e = S.F (G.owner e) D e := by
  rw [C0, Finset.sum_apply]
  exact Finset.sum_eq_single (G.owner e) (fun c _ hc => S.own c D e (Ne.symm hc))
    (fun h => absurd (Finset.mem_univ _) h)

theorem syn_congr {E E' : G.Ed → ZMod 2} {v : G.V} (h : ∀ e : G.Ed, v ∈ e.ends → E e = E' e) :
    syn E v = syn E' v := by
  simp only [syn, psyn_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hv : v ∈ f.ends
  · rw [h f hv]
  · simp [hv]

variable {S}

/-- Agreement on `Nbhd c` gives agreement of the stage-1 outputs of every block of `N_1(c)`. -/
theorem F_congr {E E' : G.Ed → ZMod 2} {c c' : G.Block} (hEE : ∀ e, G.Nbhd c e → E e = E' e)
    (hc' : G.blockDist c' c ≤ 1) : S.F c' (syn E) = S.F c' (syn E') :=
  S.loc c' _ _ fun v hv => syn_congr fun e he => hEE e ⟨v, he, c', hc', hv⟩

theorem C0_congr {E E' : G.Ed → ZMod 2} {c : G.Block} (hEE : ∀ e, G.Nbhd c e → E e = E' e) {e : G.Ed}
    (he : G.blockDist (G.owner e) c ≤ 1) : S.C0 (syn E) e = S.C0 (syn E') e := by
  rw [C0_apply, C0_apply, F_congr hEE he]

theorem Fcfg_congr {E E' : G.Ed → ZMod 2} {c : G.Block} (hEE : ∀ e, G.Nbhd c e → E e = E' e) {e : G.Ed}
    (he : G.blockDist (G.owner e) c ≤ 1) : S.Fcfg E e = S.Fcfg E' e := by
  simp only [Fcfg, Pi.add_apply]
  rw [C0_congr hEE he, hEE e ⟨G.lowEnd e, G.lowEnd_mem_ends e, G.owner e, he, by
    rw [S3Geom.owner, G.distVB_blockOf]; exact Nat.zero_le _⟩]

theorem resid_congr {E E' : G.Ed → ZMod 2} {c : G.Block} (hEE : ∀ e, G.Nbhd c e → E e = E' e) {v : G.V}
    (hv : G.blockOf v = c) : S.resid E v = S.resid E' v := by
  have hsyn : syn E v = syn E' v := syn_congr fun e he => hEE e ⟨v, he, c, by
    rw [G.blockDist_self]; exact Nat.zero_le _, by rw [← hv, G.distVB_blockOf]; exact Nat.zero_le _⟩
  simp only [resid, Pi.add_apply]
  rw [hsyn]
  congr 1
  rw [psyn_apply, psyn_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hf : v ∈ f.ends
  · rw [C0_congr hEE (hv ▸ G.blockDist_owner f hf)]
  · simp [hf]

theorem stepIn_congr {E E' : G.Ed → ZMod 2} {c : G.Block} (hEE : ∀ e, G.Nbhd c e → E e = E' e) :
    S.stepIn E c = S.stepIn E' c := by
  funext a b
  apply propext
  simp only [stepIn]
  refine and_congr_right fun ha => and_congr_right fun hb => exists_congr fun e => ?_
  refine and_congr_right fun hends => and_congr_right fun _ => ?_
  have hlow : G.lowEnd e = a ∨ G.lowEnd e = b := by
    have := G.lowEnd_mem_ends e
    rw [hends] at this
    simpa using this
  have hown : G.blockDist (G.owner e) c ≤ 1 := by
    rcases hlow with h | h <;> simp only [S3Geom.owner, h] <;> assumption
  rw [Fcfg_congr hEE hown]

/-- **Locality**: the bad event of `c` depends only on the errors on `Nbhd c`. -/
theorem bad_local {E E' : G.Ed → ZMod 2} {c : G.Block} (hEE : ∀ e, G.Nbhd c e → E e = E' e) :
    S.bad E c ↔ S.bad E' c := by
  unfold bad flagged long
  rw [stepIn_congr hEE]
  refine or_congr (exists_congr fun v => and_congr_right fun hv => ?_) Iff.rfl
  rw [resid_congr hEE hv]

variable (S)

/-! ## Hypothesis (H) -/

/-- The per-block hypothesis (H) at rate `q` with block bound `ε`: for every set `T` of blocks in the sampled rows at
pairwise block distance at least `D`, `P(all of T bad) ≤ ε^{|T|}`. -/
def HypH (q ε : ℝ) : Prop :=
  ∀ T : Finset G.Block, (∀ c ∈ T, G.sampledRow c) →
    (∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → G.D ≤ G.blockDist c c') →
      prob (bernProd q) (fun E => ∀ c ∈ T, S.bad E c) ≤ ε ^ T.card

/-- Per-block bounds on the sampled rows give Hypothesis (H) (independence at block distance `≥ D`). -/
theorem hypH_of_block_bound {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hblock : ∀ c, G.sampledRow c → prob (bernProd q) (fun E => S.bad E c) ≤ ε) : S.HypH q ε := by
  intro T hrow hsep
  rw [prob_forall_eq_prod q T (fun c e => G.Nbhd c e)
    (fun c hc c' hc' hne e h1 h2 => G.nbhd_disjoint (hsep c hc c' hc' hne) h1 h2)
    (fun c E => S.bad E c) (fun c _ E E' hEE => bad_local hEE)]
  calc ∏ c ∈ T, prob (bernProd q) (fun E => S.bad E c)
      ≤ ∏ _c ∈ T, ε := Finset.prod_le_prod₀ (fun c _ => prob_nonneg (bernProd_nonneg hq0 hq1) _)
        (fun c hc => hblock c (hrow c hc))
    _ = ε ^ T.card := Finset.prod_const ε

end Stage1

end QECML
