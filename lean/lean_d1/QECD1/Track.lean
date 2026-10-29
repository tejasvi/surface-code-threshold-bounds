import QECD1.WitnessBranch
import QECD1.Keys

/-!
# The family automaton tracks the axis displacement

Along a part of a route, the family automaton of axis `i` is in one of three kinds of state:
* `B` (0) at the root, with displacement 0;
* `A(z)` (index `z + 17`, `|z| ≤ 16`) after steps, when the displacement of the current block from the part's root
  along axis `i` is `z`;
* `Asp` (34), once that displacement has reached `|z| ≥ Sw`.

`Tracks m z` records this. Steps keep it (`tracks_step`), so do step words (`tracks_pathToks`), and `zOf m = z`
outside `Asp`.

So at the mark position `r` of the witness branch (WitnessBranch), the state `q` tracks `z = (r - e*)_i`. If the
witness condition `Sw ≤ |z + Σ w_i|` holds, the key's witness weight is `ε^{|w|}` (`witW_eq_of_tracks`). It is the
untilted weight of the walk, at `Asp` as well (all walks).
-/

namespace QECD1

open QECD1.Bld

/-- State `m` of the family automaton tracks the axis displacement `z`. -/
def Tracks (m : ℕ) (z : ℤ) : Prop := m = 34 ∨ (1 ≤ m ∧ m ≤ 33 ∧ (m : ℤ) = z + 17) ∨ (m = 0 ∧ z = 0)

theorem coord_jIdx (i : Fin 3) (v : V3) (hv : v ∈ S0) : (jIdx (coord i v) : ℤ) = coord i v + 8 := by
  have := coord_natAbs_le i v hv
  unfold jIdx
  omega

/-- **Steps keep the tracking.** -/
theorem tracks_step (i : Fin 3) {m : ℕ} {z : ℤ} (hm : Tracks m z) {v : V3} (hv : v ∈ S0) :
    Tracks (routeNext i m (Tok.step v)) (z + coord i v) := by
  have hj := coord_jIdx i v hv
  have hjl := jIdx_lt i v hv
  rcases hm with h34 | ⟨h1, h33, hz⟩ | ⟨h0, hz⟩
  · left
    subst h34
    simp [routeNext]
  · simp only [routeNext]
    rw [if_neg (by omega), if_pos h33, aNext_eq]
    split_ifs with hc
    · left; rfl
    · right; left
      refine ⟨by omega, by omega, ?_⟩
      push_cast [Nat.cast_sub (show 8 ≤ m + jIdx (coord i v) by omega)]
      omega
  · subst h0
    subst hz
    have e : routeNext i 0 (Tok.step v) = jIdx (coord i v) + 9 := by simp [routeNext]
    rw [e]
    right; left
    refine ⟨by omega, by omega, ?_⟩
    push_cast
    omega

theorem famNext_step (i : Fin 3) {m : ℕ} (hm : m < 52) (v : V3) :
    (fam3 i).next m (Tok.step v) = routeNext i m (Tok.step v) := by
  show famNext i m (Tok.step v) = _
  unfold famNext
  rw [if_pos hm, if_neg (by simp)]

theorem tracks_lt {m : ℕ} {z : ℤ} (h : Tracks m z) : m < 52 := by
  rcases h with h | ⟨_, h, _⟩ | ⟨h, _⟩ <;> omega

/-- **Step words keep the tracking**: from a tracked state, after the steps along `cur :: bs` the state tracks the
displacement plus `(last - cur)_i`. -/
theorem tracks_pathToks (i : Fin 3) {S : Finset V3} (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Const.D ≤ dist3 p q) :
    ∀ (cur : V3) (bs : List V3) (m : ℕ) (z : ℤ), Tracks m z →
      List.IsChain (selGraph S Const.A0).Adj (cur :: bs) →
      Tracks ((fam3 i).stAfter m (pathToks cur bs))
        (z + coord i ((cur :: bs).getLast (List.cons_ne_nil _ _) - cur))
  | cur, [], m, z, hm, _ => by
    simp only [List.getLast_singleton, sub_self]
    have : coord i (0 : V3) = 0 := by fin_cases i <;> rfl
    rw [this, add_zero]
    exact hm
  | cur, b :: bs, m, z, hm, hch => by
    rw [List.isChain_cons_cons] at hch
    obtain ⟨hadj, hrest⟩ := hch
    obtain ⟨hc, hb, hne, hd⟩ := selGraph_adj.1 hadj
    have hv : b - cur ∈ S0 := sep_step_mem_S0 hsep hc hb hne hd
    have hm' := tracks_step i hm hv
    have ih := tracks_pathToks i hsep b bs _ _ hm' hrest
    show Tracks ((fam3 i).stAfter ((fam3 i).next m (Tok.step (b - cur))) (pathToks b bs)) _
    rw [famNext_step i (tracks_lt hm)]
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    have hsplit : coord i ((b :: bs).getLast (List.cons_ne_nil _ _) - cur) =
        coord i (b - cur) + coord i ((b :: bs).getLast (List.cons_ne_nil _ _) - b) := by
      fin_cases i <;> simp [coord] <;> ring
    rw [hsplit, ← add_assoc]
    exact ih

theorem zOf_of_tracks {m : ℕ} {z : ℤ} (h : Tracks m z) (h34 : m ≠ 34) : zOf m = z := by
  rcases h with h | ⟨h1, h33, hz⟩ | ⟨h0, hz⟩
  · exact absurd h h34
  · unfold zOf
    rw [if_neg (by omega), if_pos h33]
    omega
  · subst h0
    rw [hz]
    rfl

/-- **The key's witness weight is the walk's untilted weight** when the witness condition holds at a tracked
state. -/
theorem witW_eq_of_tracks (i : Fin 3) {q : ℕ} {z : ℤ} (hq : Tracks q z) (w : List V3)
    (hcond : Const.Sw ≤ (z + (w.map (coord i)).sum).natAbs) : witW i q (Sum.inl w) = eps ^ w.length := by
  simp only [witW]
  split_ifs with h34
  · rfl
  · unfold witWt
    rw [zOf_of_tracks hq h34, if_pos hcond, mul_one]

end QECD1
