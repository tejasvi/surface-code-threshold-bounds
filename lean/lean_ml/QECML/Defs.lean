import Mathlib

/-!
# Decoding at code capacity: definitions

* `bern q`, `bernProd q`: i.i.d. Bernoulli(`q`) weights on bit strings `ι → ZMod 2`.
* A decoding problem is a weight `P : Ω → ℝ` on a finite error space `Ω`, a syndrome map `syn : Ω → S` and a
  logical class map `cls : Ω → C`.
* Decoders: deterministic (`S → C`), with a finite random seed, randomized (a stochastic kernel `S → C → ℝ`), and
  decoders that output a correction. Failure probabilities are finite sums over `Ω`.
* `IsML`, `mlDec`, `pML`: maximum-likelihood decoding and the optimal failure probability.
* `PEdge w h`, `psyn`, `pcls`: the matching graph of one error sector of the planar code with `w + 1` columns and
  `h + 1` rows of checks (rough top and bottom sides with half-edges to `b₁` and `b₂`, smooth left and right
  sides), its syndrome map and its logical class (the parity at `b₁`).
-/

open Finset

namespace QECML

/-! ## Bernoulli weights -/

/-- Weight of one bit under Bernoulli(`q`). -/
def bern (q : ℝ) (x : ZMod 2) : ℝ := if x = 0 then 1 - q else q

/-- The i.i.d. Bernoulli(`q`) weight of a configuration. -/
def bernProd {ι : Type*} [Fintype ι] (q : ℝ) (e : ι → ZMod 2) : ℝ := ∏ i, bern q (e i)

/-! ## Decoders and failure probabilities -/

section Decoding

variable {Ω S C : Type*} [Fintype Ω] [DecidableEq S] [DecidableEq C]

/-- Failure probability of a deterministic decoder `dec : S → C`. -/
def pFail (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (dec : S → C) : ℝ :=
  ∑ ω, if dec (syn ω) = cls ω then 0 else P ω

/-- Joint weight of the syndrome `s` and the class `c`. -/
def joint (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (s : S) (c : C) : ℝ :=
  ∑ ω, if syn ω = s ∧ cls ω = c then P ω else 0

/-- Maximum-likelihood decoders: every syndrome is decoded to a class of maximal joint weight (any tie rule). -/
def IsML (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (dec : S → C) : Prop :=
  ∀ s c, joint P syn cls s c ≤ joint P syn cls s (dec s)

/-- Failure probability of a decoder `dec r` whose seed `r` has law `ρ`, independently of the error. -/
def pFailSeed {R : Type*} [Fintype R] (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (ρ : R → ℝ)
    (dec : R → S → C) : ℝ :=
  ∑ ω, ∑ r, if dec r (syn ω) = cls ω then 0 else P ω * ρ r

/-- A randomized decoder: for each syndrome `s`, a probability distribution `δ s` on the classes. -/
structure RDecoder (S C : Type*) [Fintype C] where
  /-- probability of answering `c` on syndrome `s` -/
  δ : S → C → ℝ
  nonneg : ∀ s c, 0 ≤ δ s c
  sum_one : ∀ s, ∑ c, δ s c = 1

/-- Failure probability of a randomized decoder. -/
def pFailR [Fintype C] (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (D : RDecoder S C) : ℝ :=
  ∑ ω, P ω * (1 - D.δ (syn ω) (cls ω))

/-- Failure probability of a decoder that outputs a correction `corr s : Ω`: it fails when the correction has the
wrong syndrome, or when the residual `ω + corr (syn ω)` has a nonzero logical class. -/
def pFailCorr [AddCommGroup Ω] [Zero C] (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (corr : S → Ω) : ℝ :=
  ∑ ω, if syn (corr (syn ω)) = syn ω ∧ cls (ω + corr (syn ω)) = 0 then 0 else P ω

variable [Fintype C] [Nonempty C]

/-- A canonical ML decoder: for each syndrome, a maximiser of the joint weight chosen by classical choice. Every ML
decoder has the same failure probability (`pFail_eq_pML`). -/
noncomputable def mlDec (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (s : S) : C :=
  Classical.choose (Finset.exists_max_image Finset.univ (joint P syn cls s) Finset.univ_nonempty)

/-- The optimal (maximum-likelihood) failure probability. -/
noncomputable def pML (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) : ℝ :=
  pFail P syn cls (mlDec P syn cls)

end Decoding

/-! ## The planar code -/

/-- Edges (qubits) of the matching graph of one error sector of the planar code with `w + 1` columns and `h + 1`
rows of checks: horizontal edges `(x,y)–(x+1,y)`, vertical edges `(x,y)–(x,y+1)`, and the half-edges `(x,0)–b₁`
(bottom) and `(x,h)–b₂` (top) of the two rough sides. The left and right sides are smooth. -/
inductive PEdge (w h : ℕ) where
  | hor (x : Fin w) (y : Fin (h + 1))
  | ver (x : Fin (w + 1)) (y : Fin h)
  | bot (x : Fin (w + 1))
  | top (x : Fin (w + 1))
  deriving DecidableEq

/-- Checks `(x, y)` with `x ≤ w` and `y ≤ h`. -/
abbrev PVert (w h : ℕ) := Fin (w + 1) × Fin (h + 1)

namespace PEdge

variable {w h : ℕ}

/-- The checks at the ends of an edge: two for a bulk edge, one for a half-edge (`b₁` and `b₂` carry no
constraint). -/
def ends : PEdge w h → Finset (PVert w h)
  | hor x y => {(x.castSucc, y), (x.succ, y)}
  | ver x y => {(x, y.castSucc), (x, y.succ)}
  | bot x => {(x, 0)}
  | top x => {(x, Fin.last h)}

/-- `PEdge w h` as a sum type (for the `Fintype` instance). -/
def equivSum : PEdge w h ≃ (Fin w × Fin (h + 1)) ⊕ (Fin (w + 1) × Fin h) ⊕ Fin (w + 1) ⊕ Fin (w + 1) where
  toFun
    | hor x y => .inl (x, y)
    | ver x y => .inr (.inl (x, y))
    | bot x => .inr (.inr (.inl x))
    | top x => .inr (.inr (.inr x))
  invFun
    | .inl (x, y) => hor x y
    | .inr (.inl (x, y)) => ver x y
    | .inr (.inr (.inl x)) => bot x
    | .inr (.inr (.inr x)) => top x
  left_inv e := by cases e <;> rfl
  right_inv e := by rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x <;> rfl

instance : Fintype (PEdge w h) := Fintype.ofEquiv _ equivSum.symm

end PEdge

/-- Syndrome map: the parity of the error at each check. -/
def psyn (w h : ℕ) : (PEdge w h → ZMod 2) →+ (PVert w h → ZMod 2) where
  toFun e v := ∑ f, (if v ∈ f.ends then 1 else 0) * e f
  map_zero' := by ext v; simp
  map_add' e e' := by ext v; simp [mul_add, Finset.sum_add_distrib]

/-- Logical class: the parity of the error on the half-edges at `b₁`. A correction with the right syndrome fails
exactly when its sum with the error has class `1`, i.e. contains a path from `b₁` to `b₂`. -/
def pcls (w h : ℕ) : (PEdge w h → ZMod 2) →+ ZMod 2 where
  toFun e := ∑ x, e (.bot x)
  map_zero' := by simp
  map_add' e e' := by simp [Finset.sum_add_distrib]

/-- ML failure probability of the planar code with `W = w + 1` columns and `H = h + 1` rows at flip rate `q`. -/
noncomputable def pMLPlanar (w h : ℕ) (q : ℝ) : ℝ := pML (bernProd q) (psyn w h) (pcls w h)

end QECML
