import QECD1.OnRouteKey

/-!
# Route words: splits, states and the excursion word

Generic facts about the route words of the skeleton, used by the general key (GenKey3).

* `keyOK_of_split`: split a valid route word as `r1 ++ r2` and add any valid witness; the result is a valid key of
  every axis. The reason: the family state after `r1` has the kind (`B`/`A`/`C`) of the route grammar's state
  (`kind_stAfter`), so `r2` is allowed from the marked copy.
* `fam3_stAfter_chainToks`: after a chain route, the family state is the state after the last cluster's word, since
  a link resets the state to `B`.
* The excursion automaton reads route words as the family automaton does (`gram_exc3_of_route3`).
  * Its weight is `ε^{length}` times the end weight, which is 1 exactly in `Asp` (`exc3_wt_eq`).
  * A chain whose last part spans at least `Sw` from its root ends in `Asp` along some axis (`exc_word_asp`).
-/

namespace QECD1

open QECD1.Bld

theorem WA.stAfter_append {σ τ : Type} (M : WA σ τ) :
    ∀ (q : σ) (r1 r2 : List τ), M.stAfter q (r1 ++ r2) = M.stAfter (M.stAfter q r1) r2
  | _, [], _ => rfl
  | q, t :: ts, r2 => by
    simp only [List.cons_append, WA.stAfter]
    exact WA.stAfter_append M (M.next q t) ts r2

/-- **The family state after a route word has the route grammar's kind**, and stays before the mark. -/
theorem kind_stAfter (i : Fin 3) :
    ∀ (ws : List Tok) (m : ℕ), m < 52 → route3.Gram (kind m) ws →
      (fam3 i).stAfter m ws < 52 ∧ kind ((fam3 i).stAfter m ws) = route3.stAfter (kind m) ws
  | [], m, hm, _ => ⟨hm, rfl⟩
  | t :: ws, m, hm, hg => by
    obtain ⟨ht, hrest⟩ := hg
    change t ∈ rToks (kind m) at ht
    rw [← routeToks_eq_rToks] at ht
    have hne : t ≠ Tok.mark := fun h => mark_notMem m (h ▸ ht)
    have hnext : (fam3 i).next m t = routeNext i m t := by
      show famNext i m t = routeNext i m t
      unfold famNext
      rw [if_pos hm, if_neg hne]
    have hk := kind_routeNext i m hm t ht
    have ih := kind_stAfter i ws _ (routeNext_lt i m t ht) (by rw [hk]; exact hrest)
    show (fam3 i).stAfter ((fam3 i).next m t) ws < 52 ∧
      kind ((fam3 i).stAfter ((fam3 i).next m t) ws) = route3.stAfter (rNext (kind m) t) ws
    rw [hnext, ← hk]
    exact ih

/-- **Any split of a valid route word, with a valid witness, is a valid key** of every axis. -/
theorem keyOK_of_split (i : Fin 3) {r1 r2 : List Tok} (hg : route3.Gram 0 (r1 ++ r2)) {wit : Wit}
    (hw : witValid i wit) : KeyOK i (r1, wit, r2) := by
  rw [WA.gram_append] at hg
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hlt, hk⟩ := kind_stAfter i r1 0 (by norm_num) hg1
  refine ⟨gram_fam3_of_route3 i r1 0 (by norm_num) hg1, mark_notMem_of_route3 r1 0 hg1, hw, ?_⟩
  refine gram_fam3_marked_of_route3 i r2 _ hlt ?_
  rw [hk]
  exact hg2

theorem fam3_next_link (i : Fin 3) {m : ℕ} (hm : m < 52) (v : V3) : (fam3 i).next m (Tok.link v) = 0 := by
  show famNext i m (Tok.link v) = 0
  simp [famNext, hm, routeNext]

/-- **After a chain route the family state is the state after the last cluster's word.** -/
theorem fam3_stAfter_chainToks (i : Fin 3) :
    ∀ (s : Seg) (ss : List Seg), route3.Gram 0 (chainToks (s :: ss)) →
      (fam3 i).stAfter 0 (chainToks (s :: ss)) =
        (fam3 i).stAfter 0 (segToks ((s :: ss).getLast (List.cons_ne_nil _ _)))
  | s, [], _ => rfl
  | s, s' :: ss, hg => by
    have e : chainToks (s :: s' :: ss) =
        segToks s ++ Tok.link (s'.root - segEnd s) :: chainToks (s' :: ss) := rfl
    rw [e] at hg ⊢
    rw [WA.gram_append] at hg
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨hlt, -⟩ := kind_stAfter i (segToks s) 0 (by norm_num) hg1
    have hg3 : route3.Gram 0 (chainToks (s' :: ss)) := hg2.2
    rw [WA.stAfter_append]
    show (fam3 i).stAfter ((fam3 i).next ((fam3 i).stAfter 0 (segToks s)) (Tok.link _)) _ = _
    rw [fam3_next_link i hlt, fam3_stAfter_chainToks i s' ss hg3]
    rfl

/-- A tracked state whose displacement has reached `Sw` is `Asp`. -/
theorem tracks_asp {m : ℕ} {z : ℤ} (h : Tracks m z) (hz : Const.Sw ≤ z.natAbs) : m = 34 := by
  rw [Const.Sw_val] at hz
  rcases h with h | ⟨_, _, _⟩ | ⟨_, hz0⟩
  · exact h
  · omega
  · subst hz0
    simp at hz

/-- **Route-grammar words are excursion words**, and the excursion automaton's state is the family automaton's. -/
theorem gram_exc3_of_route3 (i : Fin 3) :
    ∀ (ws : List Tok) (m : ℕ), m < 52 → route3.Gram (kind m) ws →
      (exc3 i).Gram m ws ∧ (exc3 i).stAfter m ws = (fam3 i).stAfter m ws
  | [], _, _, _ => ⟨trivial, rfl⟩
  | t :: ws, m, hm, hg => by
    obtain ⟨ht, hrest⟩ := hg
    change t ∈ rToks (kind m) at ht
    rw [← routeToks_eq_rToks] at ht
    have hne : t ≠ Tok.mark := fun h => mark_notMem m (h ▸ ht)
    have hnext : (fam3 i).next m t = routeNext i m t := by
      show famNext i m t = routeNext i m t
      unfold famNext
      rw [if_pos hm, if_neg hne]
    have hk := kind_routeNext i m hm t ht
    have ih := gram_exc3_of_route3 i ws _ (routeNext_lt i m t ht) (by rw [hk]; exact hrest)
    refine ⟨⟨ht, ih.1⟩, ?_⟩
    show (exc3 i).stAfter (routeNext i m t) ws = (fam3 i).stAfter ((fam3 i).next m t) ws
    rw [hnext]
    exact ih.2

/-- The excursion weight: `ε` per token, times the end weight (1 in `Asp`, else 0). -/
theorem exc3_wt_eq (i : Fin 3) :
    ∀ (q : ℕ) (ws : List Tok), (exc3 i).wt q ws = eps ^ ws.length * (exc3 i).e ((exc3 i).stAfter q ws)
  | q, [] => by simp [WA.wt, WA.stAfter]
  | q, t :: ts => by
    show eps * (exc3 i).wt ((exc3 i).next q t) ts =
      eps ^ (ts.length + 1) * (exc3 i).e ((exc3 i).stAfter ((exc3 i).next q t) ts)
    rw [exc3_wt_eq i _ ts, pow_succ]
    ring

/-- **The excursion word ends in `Asp`** along an axis where its last part spans at least `Sw` from its root (an
actual block, R0). Its weight is then `ε^{length}`. -/
theorem exc_word_asp (F : Finset V3) (s : Seg) (ss : List Seg) (hok : ∀ t ∈ s :: ss, SegOK F t)
    (hg : route3.Gram 0 (chainToks (s :: ss))) {sl : Seg}
    (hsl : (s :: ss).getLast (List.cons_ne_nil _ _) = sl) (hspan : Const.Sw ≤ linf (segEnd sl - sl.root)) :
    ∃ i : Fin 3, (exc3 i).Gram 0 (chainToks (s :: ss)) ∧
      (exc3 i).wt 0 (chainToks (s :: ss)) = eps ^ (chainToks (s :: ss)).length := by
  have hslok : SegOK F sl := hok sl (hsl ▸ List.getLast_mem _)
  -- the last part is a path: its span is positive
  have hrest : sl.rest ≠ [] := by
    intro h
    have h1 : segEnd sl = sl.root := by
      unfold segEnd
      simp [h]
    rw [h1, sub_self] at hspan
    simp [linf, Const.Sw_val] at hspan
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, Const.Sw ≤ (coord i (segEnd sl - sl.root)).natAbs := by
    simp only [linf, le_max_iff] at hspan
    rcases hspan with h | h | h
    · exact ⟨0, by simpa [coord] using h⟩
    · exact ⟨1, by simpa [coord] using h⟩
    · exact ⟨2, by simpa [coord] using h⟩
  have hge := gram_exc3_of_route3 i _ 0 (by norm_num) hg
  refine ⟨i, hge.1, ?_⟩
  rw [exc3_wt_eq, hge.2, fam3_stAfter_chainToks i s ss hg, hsl]
  have hseg : segToks sl = pathToks sl.root sl.rest := by
    unfold segToks
    rw [if_neg hrest]
  rw [hseg]
  have ht := tracks_pathToks i hslok.sep sl.root sl.rest 0 0 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hslok.chain
  rw [zero_add] at ht
  have h34 := tracks_asp ht hi
  rw [h34]
  simp [exc3]

end QECD1
