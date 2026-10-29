import QECD1.Track
import QECD1.RouteFam

/-!
# An on-route family key from the skeleton (single route part)

This is the encoding step for the simplest family shape: one route part (one cluster) carrying the witness. The
data:
* the part is a cluster with selection `S`, rooted at the actual odd block `e` (R0);
* its route is a simple selection path `P = e :: P'`;
* `w` is a flagged block of another level-1 component than `e`, covered within `D - 1` by the selected block `sw`.

`onroute_key` builds a family key `(r1, w', r2)` of some axis `i` with:
* `KeyOK i`: the route word up to the mark position `r` (`witness_branch`), the witness walk from `r` to `sw`, and
  the route word after `r`, read from the marked copy;
* key weight `wtPre r1 · ε^{|w'|} · wt r2` (`witW_eq_of_tracks`): the walk has untilted weight, and the witness
  condition holds along the axis `i` given by `witness_axis` with `witness_span` (Sw = 17);
* the route blocks together with the witness blocks are pairwise `D`-separated (`branch_blocks_sep`).

The general family (a chain of route parts with the witness in one of them, or an off-route witness through an
excursion) splits the chain route of `fam_route3` at the witness part in the same way.
-/

namespace QECD1

open QECD1.Bld

/-- Route-grammar words are words of the marked copy of the family automaton. -/
theorem gram_fam3_marked_of_route3 (i : Fin 3) :
    ∀ (ws : List Tok) (m : ℕ), m < 52 → route3.Gram (kind m) ws → (fam3 i).Gram (m + 52) ws
  | [], _, _, _ => trivial
  | t :: ws, m, hm, hg => by
    obtain ⟨ht, hrest⟩ := hg
    change t ∈ rToks (kind m) at ht
    rw [← routeToks_eq_rToks] at ht
    refine ⟨?_, ?_⟩
    · show t ∈ famToks (m + 52)
      unfold famToks
      rw [if_neg (by omega), show m + 52 - 52 = m by omega]
      exact ht
    · have hnext : (fam3 i).next (m + 52) t = routeNext i m t + 52 := by
        show famNext i (m + 52) t = _
        unfold famNext
        rw [if_neg (by omega), show m + 52 - 52 = m by omega]
      rw [hnext]
      refine gram_fam3_marked_of_route3 i ws _ (routeNext_lt i m t ht) ?_
      rw [kind_routeNext i m hm t ht]
      exact hrest

theorem kind_of_tracks {m : ℕ} {z : ℤ} (h : Tracks m z) : kind m = 0 ∨ kind m = 1 := by
  rcases h with h | ⟨h1, h33, _⟩ | ⟨h0, _⟩
  · right; subst h; rfl
  · right; exact kind_eq_one h1 (by omega)
  · left; subst h0; rfl

/-- The route word from the part's root `e` up to the mark position `r`, the route being `pre ++ r :: post`. -/
def prefixToks (e : V3) (pre : List V3) (r : V3) : List Tok :=
  match pre with
  | [] => []
  | _ :: pre' => pathToks e (pre' ++ [r])

theorem prefix_props (i : Fin 3) {S : Finset V3} (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Const.D ≤ dist3 p q)
    {e r : V3} {P' pre post : List V3} (hsplit : e :: P' = pre ++ r :: post)
    (hPch : List.IsChain (selGraph S Const.A0).Adj (e :: P')) :
    route3.Gram 0 (prefixToks e pre r) ∧ Tracks ((fam3 i).stAfter 0 (prefixToks e pre r)) (coord i (r - e)) := by
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at hsplit
    obtain ⟨hre, _⟩ := hsplit
    refine ⟨trivial, ?_⟩
    show Tracks 0 (coord i (r - e))
    rw [← hre]
    right; right
    refine ⟨rfl, ?_⟩
    fin_cases i <;> simp [coord]
  | cons a pre' =>
    simp only [List.cons_append, List.cons.injEq] at hsplit
    obtain ⟨hae, hP'⟩ := hsplit
    have hch : List.IsChain (selGraph S Const.A0).Adj (e :: (pre' ++ [r])) := by
      have h1 := hPch
      rw [hP', show e :: (pre' ++ r :: post) = (e :: (pre' ++ [r])) ++ post by simp] at h1
      exact List.IsChain.left_of_append h1
    show route3.Gram 0 (pathToks e (pre' ++ [r])) ∧ Tracks ((fam3 i).stAfter 0 (pathToks e (pre' ++ [r]))) _
    refine ⟨pathToks_gram' hsep 0 (by norm_num) e (pre' ++ [r]) hch, ?_⟩
    have ht := tracks_pathToks i hsep e (pre' ++ [r]) 0 0 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hch
    have hl : (e :: (pre' ++ [r])).getLast (List.cons_ne_nil _ _) = r := by simp
    rw [hl, zero_add] at ht
    exact ht

/-- **An on-route key from one route part.** -/
theorem onroute_key (F L : Finset V3) {K S : Finset V3} {e : V3} (hS : IsSelection3 K S e Const.D Const.A0)
    (P' : List V3) (hPch : List.IsChain (selGraph S Const.A0).Adj (e :: P'))
    {w sw : V3} (he : e ∈ L) (hw : w ∈ L) (hdiff : ¬ SameComp L Const.a1 e w) (hsw : sw ∈ S)
    (hcov : dist3 w sw ≤ Const.D - 1) :
    ∃ (i : Fin 3) (r1 : List Tok) (wd : List V3) (r2 : List Tok),
      KeyOK i (r1, Sum.inl wd, r2) ∧
      keyWt i (r1, Sum.inl wd, r2) =
        (fam3 i).wtPre 0 r1 * eps ^ wd.length * (fam3 i).wt ((fam3 i).stAfter 0 r1 + 52) r2 := by
  have hsep := hS.2.2.1
  obtain ⟨r, suf, hrP, _, _, hbch, hblast, _⟩ := witness_branch hS P' hsw
  have hspan := witness_span L he hw hdiff hcov
  obtain ⟨i, hcond⟩ := witness_axis e r sw suf hblast hspan
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hrP
  obtain ⟨hg1, htr⟩ := prefix_props i hsep hsplit hPch
  have hpostch : List.IsChain (selGraph S Const.A0).Adj (r :: post) := by
    have h1 := hPch
    rw [hsplit] at h1
    exact List.IsChain.right_of_append h1
  have hg2r : route3.Gram (kind ((fam3 i).stAfter 0 (prefixToks e pre r))) (pathToks r post) := by
    rcases kind_of_tracks htr with hk | hk <;> rw [hk]
    · exact pathToks_gram' hsep 0 (by norm_num) r post hpostch
    · exact pathToks_gram' hsep 1 le_rfl r post hpostch
  refine ⟨i, prefixToks e pre r, diffs r suf, pathToks r post, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact gram_fam3_of_route3 i _ 0 (by norm_num) hg1
  · exact mark_notMem_of_route3 _ 0 hg1
  · show ∀ v ∈ diffs r suf, v ∈ S0
    exact diffs_mem_S0 hsep r suf hbch
  · exact gram_fam3_marked_of_route3 i _ _ (tracks_lt htr) hg2r
  · unfold keyWt
    simp only
    rw [witW_eq_of_tracks i htr (diffs r suf) hcond]

/-- **The route blocks and the witness blocks are pairwise `D`-separated**: the route path `e :: P'` and the branch
`r :: suf` of `witness_branch` are simple paths of the selection, and `suf` avoids the route. -/
theorem branch_blocks_sep {K S : Finset V3} {e : V3} (hS : IsSelection3 K S e Const.D Const.A0) (P' : List V3)
    (hPnd : (e :: P').Nodup) (hPS : ∀ x ∈ e :: P', x ∈ S) {r : V3} {suf : List V3}
    (hsufP : ∀ y ∈ suf, y ∉ e :: P') (hbnd : (r :: suf).Nodup) (hsufS : ∀ y ∈ suf, y ∈ S) :
    ((e :: P') ++ suf).Pairwise (fun a b => Const.D ≤ dist3 a b) := by
  have hnd : ((e :: P') ++ suf).Nodup := by
    rw [List.nodup_append]
    refine ⟨hPnd, (List.nodup_cons.1 hbnd).2, ?_⟩
    intro a ha b hb hab
    subst hab
    exact hsufP a hb ha
  refine hnd.imp_of_mem fun {a b} ha hb hne => hS.2.2.1 a ?_ b ?_ hne
  · rcases List.mem_append.1 ha with h | h
    · exact hPS a h
    · exact hsufS a h
  · rcases List.mem_append.1 hb with h | h
    · exact hPS b h
    · exact hsufS b h

end QECD1
