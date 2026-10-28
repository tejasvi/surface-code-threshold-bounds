import QECML.TwoD.T2Transfer

/-!
# The T2 summation: the skeleton class meets the transfer

* `tailOK_of`: the tail of a valid skeleton (its family keys after the bottom cover, the top part) is a valid tail
  (`(R)` on the jumps by index, as in `T2Sk.OK`; every family valid; the top route a grammar word).
* `bot_sum_le`: the bottom routes from a block (grammar words that do not end with a link) weigh at most `1.81`.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-- The tail of a valid skeleton is a valid tail. -/
theorem tailOK_of (hD : G.D = 5) (et : G.Block) (mst : List G.Move) (tf : Bool)
    (htop : tf = true → GramFrom G.D (G.D - 1 + 4) (G.D - 1 + 12) .A et mst)
    (htopF : tf = false → mst = [] ∧ et.2.val + 1 = G.ny) :
    ∀ (fams : List (G.CRoute × G.Wit)) (ex : Bool) (c : G.Block),
      (∀ f ∈ fams, f.1.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) ∧ f.2.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) (12 + 2 - G.D) f.1) →
      (∀ i (hi : i < (jumpsFrom c fams et).length), (ex = false ∨ i ≠ 0) →
        (tf = true ∨ i + 1 ≠ (jumpsFrom c fams et).length) →
          12 + 2 - G.D ≤ G.blockDist ((jumpsFrom c fams et)[i]).1 ((jumpsFrom c fams et)[i]).2) →
      TailOK ex c (fams.map famKey) et mst tf
  | [], ex, c, _, hR => by
    show TopOK ex c et mst tf
    unfold TopOK
    cases tf with
    | true =>
      rw [ite_eq_left rfl]
      refine ⟨fun hex => ?_, htop rfl⟩
      have h := hR 0 (by simp [jumpsFrom_nil]) (Or.inl hex) (Or.inl rfl)
      simp only [jumpsFrom_nil, List.getElem_cons_zero] at h
      rw [hD] at h
      exact h
    | false =>
      rw [ite_eq_right (by simp)]
      exact htopF rfl
  | f :: rest, ex, c, hfam, hR => by
    have hlen : (jumpsFrom c (f :: rest) et).length = (jumpsFrom f.1.last rest et).length + 1 := by
      rw [jumpsFrom_cons, List.length_cons]
    have hlen1 : 1 ≤ (jumpsFrom f.1.last rest et).length := by
      simp [jumpsFrom]
    refine ⟨fun hex => ?_, ⟨f, rfl, rfl, hfam f List.mem_cons_self⟩, ?_⟩
    · have h := hR 0 (by omega) (Or.inl hex) (Or.inr (by omega))
      simp only [jumpsFrom_cons, List.getElem_cons_zero] at h
      rw [hD] at h
      exact h
    · refine tailOK_of hD et mst tf htop htopF rest false f.1.last
        (fun g hg => hfam g (List.mem_cons_of_mem _ hg)) fun i hi _ htf => ?_
      have h := hR (i + 1) (by omega) (Or.inr (by omega)) (by
        rcases htf with h | h
        · exact Or.inl h
        · exact Or.inr (by omega))
      simp only [jumpsFrom_cons, List.getElem_cons_succ] at h
      exact h

/-- The final state of a word from `A` that does not end with a link is not `B`. -/
theorem finalSt_ne_B : ∀ (X : GState) (cur : G.Block) (ms : List G.Move), (ms = [] → X ≠ .B) →
    (∀ m ∈ ms.getLast?, ¬ m.isLink) → finalSt X cur ms ≠ .B
  | X, _, [], hX, _ => hX rfl
  | _, cur, [m], _, hl => by
    have hm : ¬ m.isLink := hl m rfl
    simp only [finalSt]
    cases m with
    | step b => simp [nextSt]
    | link b => exact absurd trivial hm
    | leaf b => simp [nextSt]
  | X, cur, m :: m' :: ms, _, hl => by
    simp only [finalSt]
    exact finalSt_ne_B (nextSt m) (nextBlk cur m) (m' :: ms) (fun h => absurd h (List.cons_ne_nil _ _))
      fun x hx => hl x (by simpa using hx)

/-- **Bottom routes**: grammar words from `A` that do not end with a link weigh at most `1.81`. -/
theorem bot_sum_le (hD : G.D = 5) (b0 : G.Block) (R : Finset (List G.Move))
    (hR : ∀ ms ∈ R, GramFrom G.D (G.D - 1 + 4) (G.D - 1 + 12) .A b0 ms ∧ ∀ m ∈ ms.getLast?, ¬ m.isLink) :
    ∑ ms ∈ R, gwt (t2g 5e-4 0.04305 0.02) b0 ms ≤ 1.81 := by
  set e : GState → ℝ := fun X => match X with | .A => 1 | .B => 0 | .C => 1 with he
  have heq : ∀ ms ∈ R, gwt (t2g 5e-4 0.04305 0.02) b0 ms = gwt (t2g 5e-4 0.04305 0.02) b0 ms * e (finalSt .A b0 ms) := by
    intro ms hms
    have hne := finalSt_ne_B .A b0 ms (fun _ => by simp) (hR ms hms).2
    have h1 : e (finalSt .A b0 ms) = 1 := by
      rw [he]
      cases h : finalSt .A b0 ms with
      | A => rfl
      | B => exact absurd h hne
      | C => rfl
    rw [h1, mul_one]
  rw [Finset.sum_congr rfl heq]
  have h1 := sum_gwtE_le G.D (G.D - 1 + 4) (G.D - 1 + 12) (t2g_nonneg (ε := 5e-4) (by norm_num) 0.04305 0.02)
    (e := e) (fun X => by rw [he]; cases X <;> norm_num) (R.sup List.length) .A b0 R
    fun ms hms => ⟨(hR ms hms).1, Finset.le_sup (f := List.length) hms⟩
  have h2 := route_noB_le hD (R.sup List.length) .A b0
  rw [he] at h1
  exact h1.trans h2

end S3Geom

end QECML
