import QECD1.SkelRoute
import QECD1.Keys

/-!
# Route words of the skeleton are route words of the family automata

The chain route (`chain_route`) produces words of the axis-free grammar `rToks`/`rNext` (states `B`, `A`, `C`).
The family automaton `fam3 i` reads the same words through its states `0..51` (`B`, `A(z)`, `Asp`, `C(z)`). Its
moves depend only on the kind of the state: `routeToks m = rToks (kind m)`, and the kind of the next state is
`rNext` of the kind.

* `kind`, `routeToks_eq_rToks`, `kind_routeNext`.
* `gram_fam3_of_route3`: a valid word of the route grammar from the kind of a state `m < 52` is an allowed word of
  `fam3 i` from `m`. In particular a chain route from `B` is an allowed route word (before the mark) of every
  axis's family automaton. Such a word is the `r1` of a family key (`KeyOK`), and has no mark.
* `mark_notMem_of_route3`: route-grammar words contain no mark.
-/

namespace QECD1

open QECD1.Bld

/-- The kind of a route state: `B` (0), `A(z)`/`Asp` (1), `C(z)` (2). -/
def kind (m : ℕ) : ℕ := if m = 0 then 0 else if m ≤ 34 then 1 else 2

theorem kind_eq_one {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 34) : kind n = 1 := by
  unfold kind
  rw [if_neg (by omega), if_pos h2]

theorem kind_eq_two {n : ℕ} (h : 35 ≤ n) : kind n = 2 := by
  unfold kind
  rw [if_neg (by omega), if_neg (by omega)]

theorem routeToks_eq_rToks (m : ℕ) : routeToks m = rToks (kind m) := by
  by_cases h0 : m = 0
  · subst h0
    simp [routeToks, rToks, kind]
  · by_cases h34 : m ≤ 34
    · rw [kind_eq_one (by omega) h34]
      simp [routeToks, rToks, h0, h34]
    · rw [kind_eq_two (by omega)]
      simp [routeToks, rToks, h0, h34]

theorem kind_routeNext (i : Fin 3) (m : ℕ) (hm : m < 52) (t : Tok) (ht : t ∈ routeToks m) :
    kind (routeNext i m t) = rNext (kind m) t := by
  unfold routeToks at ht
  split_ifs at ht with h0 h34
  · subst h0
    rcases Finset.mem_union.1 ht with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      have := jIdx_lt i v hv
      have e : routeNext i 0 (Tok.step v) = jIdx (coord i v) + 9 := by simp [routeNext]
      show kind (routeNext i 0 (Tok.step v)) = 1
      rw [e]
      exact kind_eq_one (by omega) (by omega)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      have := jIdx_lt i v hv
      show kind (jIdx (coord i v) + 35) = 2
      exact kind_eq_two (by omega)
  · rcases Finset.mem_union.1 ht with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      have hj := jIdx_lt i v hv
      show kind (routeNext i m (Tok.step v)) = 1
      simp only [routeNext, if_neg h0]
      split_ifs with hA
      · rw [aNext_eq]
        split_ifs with hc
        · exact kind_eq_one (by norm_num) (by norm_num)
        · exact kind_eq_one (by omega) (by omega)
      · exact kind_eq_one (by norm_num) (by norm_num)
    · obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 h
      show kind 0 = 0
      rfl
  · obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 ht
    show kind 0 = 0
    rfl


theorem mark_notMem_rToks (q : ℕ) : Tok.mark ∉ rToks q := by
  unfold rToks
  split_ifs <;> simp

/-- **Route-grammar words are family route words.** -/
theorem gram_fam3_of_route3 (i : Fin 3) :
    ∀ (ws : List Tok) (m : ℕ), m < 52 → route3.Gram (kind m) ws → (fam3 i).Gram m ws
  | [], _, _, _ => trivial
  | t :: ws, m, hm, hg => by
    obtain ⟨ht, hrest⟩ := hg
    change t ∈ rToks (kind m) at ht
    rw [← routeToks_eq_rToks] at ht
    have hne : t ≠ Tok.mark := fun h => mark_notMem m (h ▸ ht)
    refine ⟨?_, ?_⟩
    · show t ∈ famToks m
      unfold famToks
      rw [if_pos hm]
      exact Finset.mem_insert_of_mem ht
    · have hnext : (fam3 i).next m t = routeNext i m t := by
        show famNext i m t = routeNext i m t
        unfold famNext
        rw [if_pos hm, if_neg hne]
      rw [hnext]
      have hlt := routeNext_lt i m t ht
      refine gram_fam3_of_route3 i ws _ hlt ?_
      rw [kind_routeNext i m hm t ht]
      exact hrest

/-- **Route-grammar words contain no mark.** -/
theorem mark_notMem_of_route3 : ∀ (ws : List Tok) (q : ℕ), route3.Gram q ws → Tok.mark ∉ ws
  | [], _, _ => List.not_mem_nil
  | t :: ws, q, hg => by
    obtain ⟨ht, hrest⟩ := hg
    intro hmem
    rcases List.mem_cons.1 hmem with h | h
    · exact mark_notMem_rToks q (h ▸ ht)
    · exact mark_notMem_of_route3 ws _ hrest h

/-- **A chain route from `B` is an allowed route word of every axis's family automaton, without a mark.** -/
theorem chain_route_fam (i : Fin 3) (ws : List Tok) (hg : route3.Gram 0 ws) :
    (fam3 i).Gram 0 ws ∧ Tok.mark ∉ ws :=
  ⟨gram_fam3_of_route3 i ws 0 (by norm_num) hg, mark_notMem_of_route3 ws 0 hg⟩

end QECD1
