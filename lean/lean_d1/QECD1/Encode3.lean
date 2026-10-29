import QECD1.GenKeyBlocks3
import QECD1.Telescope

/-!
# `Encoding3DRooted` for skeletons: the weight side

A skeleton is a landing root, an axis and a key (`Skel3`). Its weight `skelW` has two factors:
* `ε` per counted block other than the root, i.e. `ε^{|r1| + witLen + |r2|}` (`keyBlocks_length`);
* the tilt `e^{λ |exit - e|₁ + s (exit - e)_y}` from the root to the route's end.

* `keyWt_ge`: the key weight dominates the skeleton weight. Steps and links weigh `tw v = ε e^{λ|v|₁ + s v_y}`,
  leaves and the witness weigh `ε` each, and the end weight is 1 because the route does not end at `B`
  (`famEnd_key`). The tilts telescope (`tw_telescope`).
* `skelEncoding`: the skeletons with `SkelOK` form an `Encoding3DRooted`. The encoding is the key itself, so
  injectivity is immediate.
* `famB3_skel`: every finite set of good skeletons with a common root weighs at most `F0s`.
* `gen_skel3`: under the hypotheses of the 3D deterministic lemma (cluster chain, W0, W1) every family has a good
  skeleton. Its counted blocks are pairwise `D`-separated flagged blocks, one per `ε` factor of its weight plus the
  root.

What remains for the full T2 bound is the decoder interface (W0, W1, chains), the strips and tails, and the
probability side.
-/

namespace QECD1

open QECD1.Bld

/-- The step and link offsets of a token word; leaves and marks do not move. -/
def movesOf : List Tok → List V3
  | [] => []
  | .step v :: ws => v :: movesOf ws
  | .link v :: ws => v :: movesOf ws
  | .leaf _ :: ws => movesOf ws
  | .mark :: ws => movesOf ws

/-- The number of leaves of a token word. -/
def leafCount : List Tok → ℕ
  | [] => 0
  | .step _ :: ws => leafCount ws
  | .link _ :: ws => leafCount ws
  | .leaf _ :: ws => leafCount ws + 1
  | .mark :: ws => leafCount ws

theorem movesOf_append : ∀ (a b : List Tok), movesOf (a ++ b) = movesOf a ++ movesOf b
  | [], _ => rfl
  | .step v :: a, b => congrArg (List.cons v) (movesOf_append a b)
  | .link v :: a, b => congrArg (List.cons v) (movesOf_append a b)
  | .leaf _ :: a, b => movesOf_append a b
  | .mark :: a, b => movesOf_append a b

theorem endOf_moves : ∀ (cur : V3) (ws : List Tok), endOf cur ws = cur + (movesOf ws).sum
  | cur, [] => by simp [endOf, movesOf]
  | cur, .step v :: ws => by
    show endOf (cur + v) ws = cur + (v :: movesOf ws).sum
    rw [endOf_moves (cur + v) ws, List.sum_cons, add_assoc]
  | cur, .link v :: ws => by
    show endOf (cur + v) ws = cur + (v :: movesOf ws).sum
    rw [endOf_moves (cur + v) ws, List.sum_cons, add_assoc]
  | cur, .leaf _ :: ws => endOf_moves cur ws
  | cur, .mark :: ws => endOf_moves cur ws

theorem length_moves : ∀ ws : List Tok, Tok.mark ∉ ws → ws.length = (movesOf ws).length + leafCount ws
  | [], _ => rfl
  | .step v :: ws, h => by
    show ws.length + 1 = (v :: movesOf ws).length + leafCount ws
    rw [length_moves ws (fun hm => h (List.mem_cons_of_mem _ hm)), List.length_cons]
    ring
  | .link v :: ws, h => by
    show ws.length + 1 = (v :: movesOf ws).length + leafCount ws
    rw [length_moves ws (fun hm => h (List.mem_cons_of_mem _ hm)), List.length_cons]
    ring
  | .leaf v :: ws, h => by
    show ws.length + 1 = (movesOf ws).length + (leafCount ws + 1)
    rw [length_moves ws (fun hm => h (List.mem_cons_of_mem _ hm))]
    ring
  | .mark :: _, h => absurd List.mem_cons_self h

/-- The family automaton's token weights along a word without a mark: the step and link tilts, `ε` per leaf. -/
theorem wtPre_fam3 (i : Fin 3) : ∀ (q : ℕ) (ws : List Tok), Tok.mark ∉ ws →
    (fam3 i).wtPre q ws = ((movesOf ws).map tw).prod * eps ^ leafCount ws
  | _, [], _ => by simp [WA.wtPre, movesOf, leafCount]
  | q, .step v :: ws, h => by
    show tokW q (Tok.step v) * (fam3 i).wtPre ((fam3 i).next q (Tok.step v)) ws = _
    rw [wtPre_fam3 i _ ws (fun hm => h (List.mem_cons_of_mem _ hm))]
    simp only [tokW, movesOf, leafCount, List.map_cons, List.prod_cons]
    ring
  | q, .link v :: ws, h => by
    show tokW q (Tok.link v) * (fam3 i).wtPre ((fam3 i).next q (Tok.link v)) ws = _
    rw [wtPre_fam3 i _ ws (fun hm => h (List.mem_cons_of_mem _ hm))]
    simp only [tokW, movesOf, leafCount, List.map_cons, List.prod_cons]
    ring
  | q, .leaf v :: ws, h => by
    show tokW q (Tok.leaf v) * (fam3 i).wtPre ((fam3 i).next q (Tok.leaf v)) ws = _
    rw [wtPre_fam3 i _ ws (fun hm => h (List.mem_cons_of_mem _ hm))]
    simp only [tokW, movesOf, leafCount, pow_succ]
    ring
  | _, .mark :: _, h => absurd List.mem_cons_self h

theorem wt_eq_wtPre {σ τ : Type} (M : WA σ τ) (q : σ) (ws : List τ) :
    M.wt q ws = M.wtPre q ws * M.e (M.stAfter q ws) := by
  have h := M.wt_append q ws []
  rw [List.append_nil] at h
  rw [h]
  rfl

/-- Family words without a mark are route-grammar words. -/
theorem route3_of_gram_fam3 (i : Fin 3) :
    ∀ (ws : List Tok) (m : ℕ), m < 52 → (fam3 i).Gram m ws → Tok.mark ∉ ws → route3.Gram (kind m) ws
  | [], _, _, _, _ => trivial
  | t :: ws, m, hm, hg, hmk => by
    obtain ⟨ht, hrest⟩ := hg
    have htm : t ≠ Tok.mark := fun h => hmk (h ▸ List.mem_cons_self)
    change t ∈ famToks m at ht
    unfold famToks at ht
    rw [if_pos hm] at ht
    have ht' : t ∈ routeToks m := (Finset.mem_insert.1 ht).resolve_left htm
    have hnext : (fam3 i).next m t = routeNext i m t := by
      show famNext i m t = routeNext i m t
      unfold famNext
      rw [if_pos hm, if_neg htm]
    refine ⟨?_, ?_⟩
    · show t ∈ rToks (kind m)
      rw [← routeToks_eq_rToks]
      exact ht'
    · show route3.Gram (rNext (kind m) t) ws
      rw [← kind_routeNext i m hm t ht']
      rw [hnext] at hrest
      exact route3_of_gram_fam3 i ws _ (routeNext_lt i m t ht') hrest
        (fun h => hmk (List.mem_cons_of_mem _ h))

/-- Words of the marked copy are route-grammar words. -/
theorem route3_of_gram_marked (i : Fin 3) :
    ∀ (ws : List Tok) (m : ℕ), m < 52 → (fam3 i).Gram (m + 52) ws → route3.Gram (kind m) ws
  | [], _, _, _ => trivial
  | t :: ws, m, hm, hg => by
    obtain ⟨ht, hrest⟩ := hg
    change t ∈ famToks (m + 52) at ht
    unfold famToks at ht
    rw [if_neg (by omega), show m + 52 - 52 = m by omega] at ht
    have hnext : (fam3 i).next (m + 52) t = routeNext i m t + 52 := by
      show famNext i (m + 52) t = _
      unfold famNext
      rw [if_neg (by omega), show m + 52 - 52 = m by omega]
    refine ⟨?_, ?_⟩
    · show t ∈ rToks (kind m)
      rw [← routeToks_eq_rToks]
      exact ht
    · show route3.Gram (rNext (kind m) t) ws
      rw [← kind_routeNext i m hm t ht]
      rw [hnext] at hrest
      exact route3_of_gram_marked i ws _ (routeNext_lt i m t ht) hrest

/-- **The route word of a valid key** is a route-grammar word. -/
theorem route3_of_keyOK (i : Fin 3) {r1 r2 : List Tok} {wit : Wit} (hk : KeyOK i (r1, wit, r2)) :
    route3.Gram 0 (r1 ++ r2) := by
  obtain ⟨g1, m1, _, g2⟩ := hk
  have h1 := route3_of_gram_fam3 i r1 0 (by norm_num) g1 m1
  obtain ⟨hlt, hk1⟩ := kind_stAfter i r1 0 (by norm_num) h1
  have h2 := route3_of_gram_marked i r2 _ hlt g2
  rw [hk1] at h2
  rw [WA.gram_append]
  exact ⟨h1, h2⟩

/-- In the marked copy the state is the unmarked state plus 52. -/
theorem stAfter_marked (i : Fin 3) : ∀ (ws : List Tok) (m : ℕ), m < 52 → route3.Gram (kind m) ws →
    (fam3 i).stAfter (m + 52) ws = (fam3 i).stAfter m ws + 52
  | [], _, _, _ => rfl
  | t :: ws, m, hm, hg => by
    obtain ⟨ht, hrest⟩ := hg
    change t ∈ rToks (kind m) at ht
    rw [← routeToks_eq_rToks] at ht
    have hne : t ≠ Tok.mark := fun h => mark_notMem m (h ▸ ht)
    have h1 : (fam3 i).next (m + 52) t = routeNext i m t + 52 := by
      show famNext i (m + 52) t = _
      unfold famNext
      rw [if_neg (by omega), show m + 52 - 52 = m by omega]
    have h2 : (fam3 i).next m t = routeNext i m t := by
      show famNext i m t = _
      unfold famNext
      rw [if_pos hm, if_neg hne]
    show (fam3 i).stAfter ((fam3 i).next (m + 52) t) ws = (fam3 i).stAfter ((fam3 i).next m t) ws + 52
    rw [h1, h2]
    exact stAfter_marked i ws _ (routeNext_lt i m t ht) (by rw [kind_routeNext i m hm t ht]; exact hrest)

/-- **The end weight of a key's suffix is 1** when the route word does not end at `B`. -/
theorem famEnd_key (i : Fin 3) {r1 r2 : List Tok} (hg : route3.Gram 0 (r1 ++ r2))
    (hpos : 1 ≤ route3.stAfter 0 (r1 ++ r2)) :
    famEnd ((fam3 i).stAfter ((fam3 i).stAfter 0 r1 + 52) r2) = 1 := by
  rw [WA.gram_append] at hg
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hlt, hk⟩ := kind_stAfter i r1 0 (by norm_num) hg1
  have hg2' : route3.Gram (kind ((fam3 i).stAfter 0 r1)) r2 := by
    rw [hk]
    exact hg2
  rw [stAfter_marked i r2 _ hlt hg2']
  obtain ⟨-, hk2⟩ := kind_stAfter i r2 _ hlt hg2'
  rw [hk] at hk2
  have hne : (fam3 i).stAfter ((fam3 i).stAfter 0 r1) r2 ≠ 0 := by
    intro h0
    rw [h0] at hk2
    have h3 : route3.stAfter 0 (r1 ++ r2) = 0 := by
      rw [WA.stAfter_append]
      exact hk2.symm
    omega
  unfold famEnd
  rw [if_neg (by omega)]

/-- **The key weight dominates the skeleton weight.** -/
theorem keyWt_ge (i : Fin 3) (e : V3) {r1 r2 : List Tok} {wit : Wit} (hk : KeyOK i (r1, wit, r2))
    (hw : keyWt i (r1, wit, r2) =
      (fam3 i).wtPre 0 r1 * eps ^ witLen wit * (fam3 i).wt ((fam3 i).stAfter 0 r1 + 52) r2)
    (hpos : 1 ≤ route3.stAfter 0 (r1 ++ r2)) :
    eps ^ (r1.length + witLen wit + r2.length) *
        Real.exp (lam * l1 (endOf e (r1 ++ r2) - e) + sT * (endOf e (r1 ++ r2) - e).2.2) ≤
      keyWt i (r1, wit, r2) := by
  have hg := route3_of_keyOK i hk
  obtain ⟨_, h1, _, h2⟩ := hk
  have hm2 := mark_notMem_marked i r2 _ (by omega) h2
  have hwt2 : (fam3 i).wt ((fam3 i).stAfter 0 r1 + 52) r2 =
      (fam3 i).wtPre ((fam3 i).stAfter 0 r1 + 52) r2 := by
    rw [wt_eq_wtPre]
    show _ * famEnd _ = _
    rw [famEnd_key i hg hpos, mul_one]
  rw [hw, hwt2, wtPre_fam3 i 0 r1 h1, wtPre_fam3 i _ r2 hm2]
  have hend : endOf e (r1 ++ r2) - e = (movesOf r1 ++ movesOf r2).sum := by
    rw [endOf_moves, movesOf_append]
    abel
  rw [hend, length_moves r1 h1, length_moves r2 hm2]
  have htel := tw_telescope (movesOf r1 ++ movesOf r2)
  rw [List.map_append, List.prod_append, List.length_append] at htel
  have hE : 0 ≤ eps := eps_nonneg
  generalize Real.exp (lam * l1 (movesOf r1 ++ movesOf r2).sum + sT * (movesOf r1 ++ movesOf r2).sum.2.2) = X
    at htel ⊢
  generalize ((movesOf r1).map tw).prod = P1 at htel ⊢
  generalize ((movesOf r2).map tw).prod = P2 at htel ⊢
  have hL : 0 ≤ eps ^ leafCount r1 * eps ^ witLen wit * eps ^ leafCount r2 :=
    mul_nonneg (mul_nonneg (pow_nonneg hE _) (pow_nonneg hE _)) (pow_nonneg hE _)
  calc eps ^ ((movesOf r1).length + leafCount r1 + witLen wit + ((movesOf r2).length + leafCount r2)) * X
      = (eps ^ ((movesOf r1).length + (movesOf r2).length) * X) *
          (eps ^ leafCount r1 * eps ^ witLen wit * eps ^ leafCount r2) := by ring
    _ ≤ (P1 * P2) * (eps ^ leafCount r1 * eps ^ witLen wit * eps ^ leafCount r2) :=
        mul_le_mul_of_nonneg_right htel hL
    _ = P1 * eps ^ leafCount r1 * eps ^ witLen wit * (P2 * eps ^ leafCount r2) := by ring

/-! ### The encoding of the skeletons -/

/-- A skeleton: a landing root, an axis and a key. -/
abbrev Skel3 := V3 × Fin 3 × Key

/-- A good skeleton: a valid key whose weight factors with `ε^{witLen}` for the witness, on a route word that does not
end at `B`. -/
def SkelOK (k : Skel3) : Prop :=
  KeyOK k.2.1 k.2.2 ∧
    keyWt k.2.1 k.2.2 = (fam3 k.2.1).wtPre 0 k.2.2.1 * eps ^ witLen k.2.2.2.1 *
      (fam3 k.2.1).wt ((fam3 k.2.1).stAfter 0 k.2.2.1 + 52) k.2.2.2.2 ∧
    1 ≤ route3.stAfter 0 (k.2.2.1 ++ k.2.2.2.2)

/-- The weight of a skeleton: `ε` per counted block other than the root, times the tilt from the root to the route's
end. -/
noncomputable def skelW (k : Skel3) : ℝ :=
  eps ^ (k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length) *
    Real.exp (lam * l1 (endOf k.1 (k.2.2.1 ++ k.2.2.2.2) - k.1) + sT * (endOf k.1 (k.2.2.1 ++ k.2.2.2.2) - k.1).2.2)

/-- **`Encoding3DRooted` for skeletons.** -/
noncomputable def skelEncoding : Encoding3DRooted Skel3 where
  root k := k.1
  fok := SkelOK
  w := skelW
  ax k := k.2.1
  enc k := k.2.2
  ok _ hk := hk.1
  le k hk := by
    obtain ⟨e, i, r1, wit, r2⟩ := k
    exact keyWt_ge i e hk.1 hk.2.1 hk.2.2
  inj k k' _ _ h1 h2 h3 := Prod.ext h1 (Prod.ext h2 h3)

/-- **`FamB3` for skeletons**: every finite set of good skeletons with a common landing root weighs at most `F0s`. -/
theorem famB3_skel (e : V3) (K : Finset Skel3) (hK : ∀ k ∈ K, k.1 = e ∧ SkelOK k) : ∑ k ∈ K, skelW k ≤ F0s :=
  famB3_rooted skelEncoding e K hK

/-- **Every family has a good skeleton.** Its counted blocks are pairwise `D`-separated flagged blocks, one per `ε`
factor of its weight plus the root. -/
theorem gen_skel3 (F L : Finset V3) (hLF : L ⊆ F) {e x : V3} (he : e ∈ L) (hx : x ∈ L)
    (hex : ∃ (n : ℕ) (f : ℕ → V3 × V3), FChain3 F L e x n f)
    (hW0 : ∀ r ∈ L, ∃ b, SameComp F Const.a0 r b ∧ Const.D ≤ dist3 r b) (hW1 : W1Hyp F L e) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ F) ∧
      (keyBlocks e k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length := by
  obtain ⟨i, r1, wit, r2, h1, h2, h3, hc, h4, h5⟩ := gen_key3_blocks F L hLF he hx hex hW0 hW1
  exact ⟨(e, i, r1, wit, r2), rfl, ⟨h1, h2, h3⟩, hc, h4, h5, keyBlocks_length i e h1⟩

end QECD1
