import QECD1.Rooting

/-!
# The 3D selection lemma (A0 = 8)

This is the 3D version of the 2D `exists_selection` (TwoD/Selection).
In each `a0`-connected cluster of blocks one selects blocks with three properties:
* the selected blocks are pairwise at least `D` apart;
* each selected block other than the root has a selected parent within `A0 = D - 1 + a0`;
* every block of the cluster lies within `D - 1` of a selected block (its cover).

The proof is metric only (`ℓ∞` on block coordinates): it takes a largest selection and shows that a block at
distance `≥ D` from it would extend it. So the 2D proof carries over verbatim.

* `dist3`: `ℓ∞` block distance on `ℤ³`, with `dist3_self`, `dist3_comm`, `dist3_triangle`.
* `exists_selection3`: the selection lemma for any `a`-connected finite set of blocks.
* `selection_A0`: at the registered values (`D = 5`, `a0 = 4`) the link length is `A0 = 8` and the cover distance
  is `D - 1 = 4`.
* `step_mem_S0`: two distinct selected blocks within `A0` of each other differ by an offset in
  `S0 = {5 ≤ |v|∞ ≤ 8}`, the step set of the family automata. The root is a block of the cluster (`r ∈ S ⊆ K`),
  which is what (R0) asks for when the cluster's root is an actual odd block.
-/

namespace QECD1

/-- `ℓ∞` distance between blocks. -/
def dist3 (a b : V3) : ℕ := linf (a - b)

theorem dist3_self (a : V3) : dist3 a a = 0 := by
  simp [dist3, linf]

theorem dist3_comm (a b : V3) : dist3 a b = dist3 b a := linf_sub_comm a b

theorem dist3_triangle (a b c : V3) : dist3 a c ≤ dist3 a b + dist3 b c := linf_sub_le a b c

/-- `S` is a selection in `K` rooted at `r` (separation `D`, link length `A`). -/
def IsSelection3 (K S : Finset V3) (r : V3) (D A : ℕ) : Prop :=
  S ⊆ K ∧ r ∈ S ∧ (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → D ≤ dist3 s s') ∧
    ∀ s ∈ S, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ dist3 x y ≤ A) r s

/-- **Selection lemma (3D).** An `a`-connected finite set of blocks has a selection rooted at any of its blocks, with
separation `D ≥ 1` and link length `D - 1 + a`, which covers it within `D - 1`. -/
theorem exists_selection3 {K : Finset V3} {a D : ℕ} (hD : 1 ≤ D) {r : V3} (hr : r ∈ K)
    (hK : ∀ x ∈ K, Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ dist3 x y ≤ a) r x) :
    ∃ S : Finset V3, IsSelection3 K S r D (D - 1 + a) ∧ ∀ x ∈ K, ∃ s ∈ S, dist3 x s ≤ D - 1 := by
  classical
  set cands := (K.powerset).filter (fun S => IsSelection3 K S r D (D - 1 + a)) with hcands
  have hne : cands.Nonempty := ⟨{r}, by
    simp only [hcands, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.singleton_subset_iff.2 hr, Finset.singleton_subset_iff.2 hr, Finset.mem_singleton_self r,
      fun s hs s' hs' hne => absurd ((Finset.mem_singleton.1 hs).trans (Finset.mem_singleton.1 hs').symm) hne,
      fun s hs => ?_⟩
    rw [Finset.mem_singleton.1 hs]⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image cands Finset.card hne
  have hSsel : IsSelection3 K S r D (D - 1 + a) := (Finset.mem_filter.1 hS).2
  refine ⟨S, hSsel, ?_⟩
  obtain ⟨hSK, hrS, hsep, hconn⟩ := hSsel
  have key : ∀ x, Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ dist3 x y ≤ a) r x →
      (∃ s ∈ S, dist3 x s ≤ D - 1) ∨
        ∃ y ∈ K, (∀ s ∈ S, D ≤ dist3 y s) ∧ ∃ s ∈ S, dist3 y s ≤ D - 1 + a := by
    intro x hx
    induction hx with
    | refl => exact Or.inl ⟨r, hrS, by rw [dist3_self]; exact Nat.zero_le _⟩
    | @tail b x' _ hstep ih =>
      obtain ⟨_, hx'K, hbx⟩ := hstep
      by_cases hclose : ∃ s ∈ S, dist3 x' s ≤ D - 1
      · exact Or.inl hclose
      · have hfar : ∀ s ∈ S, D ≤ dist3 x' s := fun s hs => by
          by_contra h
          exact hclose ⟨s, hs, by omega⟩
        rcases ih with ⟨s, hs, hbs⟩ | hy
        · refine Or.inr ⟨x', hx'K, hfar, s, hs, ?_⟩
          have := dist3_triangle x' b s
          rw [dist3_comm x' b] at this
          omega
        · exact Or.inr hy
  intro x hxK
  rcases key x (hK x hxK) with hclose | ⟨z, hzK, hzfar, s, hs, hzs⟩
  · exact hclose
  · exfalso
    have hzS : z ∉ S := fun h => by
      have := hzfar z h
      rw [dist3_self] at this
      omega
    have hmono : ∀ t, Relation.ReflTransGen (fun p q => p ∈ S ∧ q ∈ S ∧ dist3 p q ≤ D - 1 + a) r t →
        Relation.ReflTransGen (fun p q => p ∈ insert z S ∧ q ∈ insert z S ∧ dist3 p q ≤ D - 1 + a) r t := by
      intro t h
      induction h with
      | refl => exact .refl
      | tail _ hbc ih' =>
        exact ih'.tail ⟨Finset.mem_insert_of_mem hbc.1, Finset.mem_insert_of_mem hbc.2.1, hbc.2.2⟩
    have hsel' : IsSelection3 K (insert z S) r D (D - 1 + a) := by
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
            rw [dist3_comm]
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
            rw [dist3_comm]; exact hzs⟩
        · exact hmono t (hconn t h)
    have hmem : insert z S ∈ cands := by
      simp only [hcands, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hsel'.1, hsel'⟩
    have := hmax _ hmem
    rw [Finset.card_insert_of_notMem hzS] at this
    omega

/-- **The selection at the registered values**: separation `D = 5`, link length `A0 = 8`, cover distance
`D - 1 = 4`. -/
theorem selection_A0 {K : Finset V3} {r : V3} (hr : r ∈ K)
    (hK : ∀ x ∈ K, Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ dist3 x y ≤ Const.a0) r x) :
    ∃ S : Finset V3, IsSelection3 K S r Const.D Const.A0 ∧ ∀ x ∈ K, ∃ s ∈ S, dist3 x s ≤ Const.D - 1 := by
  have h := exists_selection3 (a := Const.a0) (D := Const.D) (by rw [Const.D_val]; norm_num) hr hK
  simpa [Const.A0] using h

/-- **Selection steps are `S0` offsets**: distinct selected blocks within `A0` differ by an offset with
`D ≤ |v|∞ ≤ A0`, i.e. in `S0`. -/
theorem step_mem_S0 {K S : Finset V3} {r : V3} (hS : IsSelection3 K S r Const.D Const.A0) {s s' : V3}
    (hs : s ∈ S) (hs' : s' ∈ S) (hne : s ≠ s') (hlink : dist3 s s' ≤ Const.A0) : s' - s ∈ S0 := by
  have hsep := hS.2.2.1 s hs s' hs' hne
  rw [S0_eq, Finset.mem_filter, mem_box]
  have h1 : linf (s' - s) = dist3 s s' := by rw [dist3, linf_sub_comm]
  rw [h1]
  exact ⟨hlink, hsep⟩

end QECD1
