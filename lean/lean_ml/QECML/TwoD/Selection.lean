import QECML.TwoD.W1

/-!
# The 2D lemma, deterministic part: selection of separated blocks

The selection step of the paper's proof: in each cluster one selects blocks so that the
selected blocks are pairwise at least `D` apart, each selected block other than the root has a selected parent
within `A0 = D - 1 + a0`, and every block of the cluster is within `D - 1` of a selected block (the greedy
breadth-first selection).

`exists_selection` proves this for any `a`-connected finite set of blocks: a selection `S` containing the root, `D`-
separated, `(D - 1 + a)`-connected through the root, and covering the set within `D - 1`. The proof takes a
largest such `S` and shows that a block at distance `≥ D` from `S` would extend it (first exit along a chain).
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-- `S` is a selection in `K` rooted at `r` (separation `D`, link length `A`). -/
def IsSelection (K S : Finset G.Block) (r : G.Block) (D A : ℕ) : Prop :=
  S ⊆ K ∧ r ∈ S ∧ (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → D ≤ G.blockDist s s') ∧
    ∀ s ∈ S, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ G.blockDist x y ≤ A) r s

/-- **Selection lemma.** An `a`-connected finite set of blocks has a selection rooted at any of its blocks, with
separation `D ≥ 1` and link length `D - 1 + a`, which covers it within `D - 1`. -/
theorem exists_selection {K : Finset G.Block} {a D : ℕ} (hD : 1 ≤ D) {r : G.Block} (hr : r ∈ K)
    (hK : ∀ x ∈ K, Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ G.blockDist x y ≤ a) r x) :
    ∃ S : Finset G.Block, IsSelection K S r D (D - 1 + a) ∧ ∀ x ∈ K, ∃ s ∈ S, G.blockDist x s ≤ D - 1 := by
  -- the candidate selections form a nonempty finite family; take one of maximal size
  set cands := (K.powerset).filter (fun S => IsSelection K S r D (D - 1 + a)) with hcands
  have hne : cands.Nonempty := ⟨{r}, by
    simp only [hcands, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.singleton_subset_iff.2 hr, Finset.singleton_subset_iff.2 hr, Finset.mem_singleton_self r,
      fun s hs s' hs' hne => absurd ((Finset.mem_singleton.1 hs).trans (Finset.mem_singleton.1 hs').symm) hne,
      fun s hs => ?_⟩
    rw [Finset.mem_singleton.1 hs]⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image cands Finset.card hne
  have hSsel : IsSelection K S r D (D - 1 + a) := (Finset.mem_filter.1 hS).2
  refine ⟨S, hSsel, ?_⟩
  obtain ⟨hSK, hrS, hsep, hconn⟩ := hSsel
  -- first exit: along a chain from r, either every block is close to S, or some block of K is far from S
  -- but within D - 1 + a of S
  have key : ∀ x, Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ G.blockDist x y ≤ a) r x →
      (∃ s ∈ S, G.blockDist x s ≤ D - 1) ∨
        ∃ y ∈ K, (∀ s ∈ S, D ≤ G.blockDist y s) ∧ ∃ s ∈ S, G.blockDist y s ≤ D - 1 + a := by
    intro x hx
    induction hx with
    | refl => exact Or.inl ⟨r, hrS, by rw [G.blockDist_self]; exact Nat.zero_le _⟩
    | @tail b x' _ hstep ih =>
      obtain ⟨_, hx'K, hbx⟩ := hstep
      by_cases hclose : ∃ s ∈ S, G.blockDist x' s ≤ D - 1
      · exact Or.inl hclose
      · have hfar : ∀ s ∈ S, D ≤ G.blockDist x' s := fun s hs => by
          by_contra h
          exact hclose ⟨s, hs, by omega⟩
        rcases ih with ⟨s, hs, hbs⟩ | hy
        · refine Or.inr ⟨x', hx'K, hfar, s, hs, ?_⟩
          have := G.blockDist_triangle x' b s
          rw [G.blockDist_comm x' b] at this
          omega
        · exact Or.inr hy
  intro x hxK
  rcases key x (hK x hxK) with hclose | ⟨z, hzK, hzfar, s, hs, hzs⟩
  · exact hclose
  · exfalso
    -- S ∪ {z} is a larger selection
    have hzS : z ∉ S := fun h => by
      have := hzfar z h
      rw [G.blockDist_self] at this
      omega
    have hmono : ∀ t, Relation.ReflTransGen (fun p q => p ∈ S ∧ q ∈ S ∧ G.blockDist p q ≤ D - 1 + a) r t →
        Relation.ReflTransGen
          (fun p q => p ∈ insert z S ∧ q ∈ insert z S ∧ G.blockDist p q ≤ D - 1 + a) r t := by
      intro t h
      induction h with
      | refl => exact .refl
      | tail _ hbc ih' =>
        exact ih'.tail ⟨Finset.mem_insert_of_mem hbc.1, Finset.mem_insert_of_mem hbc.2.1, hbc.2.2⟩
    have hsel' : IsSelection K (insert z S) r D (D - 1 + a) := by
      refine ⟨Finset.insert_subset hzK hSK, Finset.mem_insert_of_mem hrS, ?_, ?_⟩
      · intro u hu u' hu' huu
        by_cases hu1 : u = z
        · subst hu1
          have hu'S : u' ∈ S := by
            rcases Finset.mem_insert.1 hu' with h | h
            · exact absurd h.symm huu
            · exact h
          exact hzfar u' hu'S
        · have huS : u ∈ S := by
            rcases Finset.mem_insert.1 hu with h | h
            · exact absurd h hu1
            · exact h
          by_cases hu2 : u' = z
          · subst hu2
            rw [G.blockDist_comm]
            exact hzfar u huS
          · have hu'S : u' ∈ S := by
              rcases Finset.mem_insert.1 hu' with h | h
              · exact absurd h hu2
              · exact h
            exact hsep u huS u' hu'S huu
      · intro t ht
        rcases Finset.mem_insert.1 ht with h | h
        · rw [h]
          exact (hmono s (hconn s hs)).tail ⟨Finset.mem_insert_of_mem hs, Finset.mem_insert_self _ _, by
            rw [G.blockDist_comm]; exact hzs⟩
        · exact hmono t (hconn t h)
    have hmem : insert z S ∈ cands := by
      simp only [hcands, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hsel'.1, hsel'⟩
    have := hmax _ hmem
    rw [Finset.card_insert_of_notMem hzS] at this
    omega

end S3Geom

end QECML
