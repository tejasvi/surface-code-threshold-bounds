import QECML.S3.Events

/-!
# Corrections inside connected regions (towards the validity of S3)

`Realizable U T`: `T` is the syndrome of an edge set lying inside the vertex set `U` (a half-edge lies inside `U`
iff its check does). If `U` is connected, every syndrome supported in `U` with even total parity is realizable
(`realizable_of_even`); if `U` also contains a check of a rough row, every syndrome supported in `U` is realizable
(`realizable_of_rough`). These are the two cases in which S3 resolves a component (validity of the decoder).
-/

open Finset

namespace QECML

namespace S3Geom

variable (G : S3Geom)

/-- Two checks are adjacent if a bulk edge joins them. -/
def adj (u v : G.V) : Prop := ∃ e : G.Ed, e.ends = {u, v} ∧ u ≠ v

theorem adj_symm {u v : G.V} (h : G.adj u v) : G.adj v u := by
  obtain ⟨e, he, hne⟩ := h
  exact ⟨e, by rw [he, Finset.pair_comm], hne.symm⟩

/-- A step of a path inside `U`. -/
def stepU (U : Set G.V) (a b : G.V) : Prop := a ∈ U ∧ b ∈ U ∧ G.adj a b

/-- `U` is connected: any two of its checks are joined by a path of adjacent checks of `U`. -/
def Conn (U : Set G.V) : Prop := ∀ u ∈ U, ∀ v ∈ U, Relation.ReflTransGen (G.stepU U) u v

/-- The edge set `X` lies inside `U`: every check of every edge of `X` is in `U`. -/
def Inside (U : Set G.V) (X : G.Ed → ZMod 2) : Prop := ∀ e, X e ≠ 0 → ∀ v ∈ e.ends, v ∈ U

/-- `T` is the syndrome of an edge set inside `U`. -/
def Realizable (U : Set G.V) (T : G.V → ZMod 2) : Prop := ∃ X, G.Inside U X ∧ psyn G.w G.h X = T

variable {G}

theorem realizable_zero (U : Set G.V) : G.Realizable U 0 :=
  ⟨0, fun _ h => absurd rfl h, map_zero _⟩

theorem realizable_add {U : Set G.V} {T1 T2 : G.V → ZMod 2} (h1 : G.Realizable U T1)
    (h2 : G.Realizable U T2) : G.Realizable U (T1 + T2) := by
  obtain ⟨X1, hi1, hs1⟩ := h1
  obtain ⟨X2, hi2, hs2⟩ := h2
  refine ⟨X1 + X2, fun e he v hv => ?_, by rw [map_add, hs1, hs2]⟩
  by_cases h : X1 e = 0
  · have h2' : X2 e ≠ 0 := by simpa [h] using he
    exact hi2 e h2' v hv
  · exact hi1 e h v hv

theorem realizable_smul {U : Set G.V} {T : G.V → ZMod 2} (h : G.Realizable U T) (a : ZMod 2) :
    G.Realizable U (a • T) := by
  rcases zmod2_cases a with rfl | rfl
  · simpa using realizable_zero U
  · simpa using h

theorem realizable_sum {U : Set G.V} {ι : Type*} (s : Finset ι) (T : ι → G.V → ZMod 2)
    (h : ∀ i ∈ s, G.Realizable U (T i)) : G.Realizable U (∑ i ∈ s, T i) :=
  Finset.sum_induction T (G.Realizable U) (fun _ _ ha hb => realizable_add ha hb) (realizable_zero U) h

theorem psyn_single (e : G.Ed) :
    psyn G.w G.h (Pi.single e 1) = fun v => if v ∈ e.ends then 1 else 0 := by
  funext v
  rw [psyn_apply]
  simp [Pi.single_apply]

/-- One bulk edge inside `U` realizes the pair of its ends. -/
theorem realizable_pair_of_adj {U : Set G.V} {u v : G.V} (hu : u ∈ U) (hv : v ∈ U) (h : G.adj u v) :
    G.Realizable U (Pi.single u 1 + Pi.single v 1) := by
  obtain ⟨e, he, hne⟩ := h
  refine ⟨Pi.single e 1, fun f hf w hw => ?_, ?_⟩
  · have hfe : f = e := by
      by_contra hfe
      simp [hfe] at hf
    subst hfe
    rw [he, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv
  · rw [psyn_single, he]
    funext w
    simp only [Finset.mem_insert, Finset.mem_singleton, Pi.add_apply, Pi.single_apply]
    by_cases h1 : w = u <;> by_cases h2 : w = v <;> simp_all

/-- A path inside `U` realizes the pair of its ends. -/
theorem realizable_pair_of_reach {U : Set G.V} {u v : G.V}
    (h : Relation.ReflTransGen (G.stepU U) u v) : G.Realizable U (Pi.single u 1 + Pi.single v 1) := by
  induction h with
  | refl =>
    have : (Pi.single u 1 + Pi.single u 1 : G.V → ZMod 2) = 0 := by
      funext w
      exact zmod2_add_self _
    rw [this]
    exact realizable_zero U
  | @tail b c _ hstep ih =>
    obtain ⟨hb, hc, hadj⟩ := hstep
    have h2 := realizable_add ih (realizable_pair_of_adj hb hc hadj)
    have hff : ∀ f : G.V → ZMod 2, f + f = 0 := fun f => funext fun w => zmod2_add_self (f w)
    have hid : (Pi.single u 1 + Pi.single c 1 : G.V → ZMod 2) =
        Pi.single u 1 + Pi.single b 1 + (Pi.single b 1 + Pi.single c 1) := by
      rw [add_assoc, ← add_assoc (Pi.single b 1), hff, zero_add]
    rw [hid]
    exact h2

theorem eq_sum_pairs (T : G.V → ZMod 2) (u0 : G.V) :
    T = (∑ v, T v) • Pi.single u0 1 + ∑ v, T v • (Pi.single u0 1 + Pi.single v 1) := by
  funext w
  have h1 : (∑ v, T v • (Pi.single u0 1 + Pi.single v 1 : G.V → ZMod 2)) w =
      (∑ v, T v) * (Pi.single u0 1 : G.V → ZMod 2) w + T w := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    congr 1
    simp [Pi.single_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1]
  rw [← add_assoc, zmod2_add_self, zero_add]

/-- In a connected region, every syndrome supported in it with even parity is realizable. -/
theorem realizable_of_even {U : Set G.V} (hU : G.Conn U) {T : G.V → ZMod 2}
    (hsupp : ∀ v, T v ≠ 0 → v ∈ U) (heven : ∑ v, T v = 0) : G.Realizable U T := by
  by_cases hne : ∃ u0, u0 ∈ U
  · obtain ⟨u0, hu0⟩ := hne
    rw [eq_sum_pairs T u0, heven, zero_smul, zero_add]
    refine realizable_sum _ _ fun v _ => ?_
    by_cases hv : T v = 0
    · rw [hv, zero_smul]
      exact realizable_zero U
    · exact realizable_smul (realizable_pair_of_reach (hU u0 hu0 v (hsupp v hv))) _
  · have hT : T = 0 := funext fun v => by
      by_contra h
      exact hne ⟨v, hsupp v h⟩
    rw [hT]
    exact realizable_zero U

/-- A check of a rough row inside `U` realizes itself through its half-edge. -/
theorem realizable_single_rough {U : Set G.V} {r : G.V} (hr : r ∈ U) (hrough : r.2 = 0 ∨ r.2 = Fin.last _) :
    G.Realizable U (Pi.single r 1) := by
  obtain ⟨rx, ry⟩ := r
  rcases hrough with h | h <;> simp only at h <;> subst h
  · refine ⟨Pi.single (PEdge.bot rx) 1, fun f hf w hw => ?_, ?_⟩
    · have hfe : f = PEdge.bot rx := by
        by_contra hfe
        simp [hfe] at hf
      subst hfe
      simp only [PEdge.ends, Finset.mem_singleton] at hw
      rw [hw]
      exact hr
    · rw [psyn_single]
      funext w
      simp [PEdge.ends, Pi.single_apply]
  · refine ⟨Pi.single (PEdge.top rx) 1, fun f hf w hw => ?_, ?_⟩
    · have hfe : f = PEdge.top rx := by
        by_contra hfe
        simp [hfe] at hf
      subst hfe
      simp only [PEdge.ends, Finset.mem_singleton] at hw
      rw [hw]
      exact hr
    · rw [psyn_single]
      funext w
      simp [PEdge.ends, Pi.single_apply]

/-- In a connected region containing a check of a rough row, every syndrome supported in it is realizable. -/
theorem realizable_of_rough {U : Set G.V} (hU : G.Conn U) {r : G.V} (hr : r ∈ U)
    (hrough : r.2 = 0 ∨ r.2 = Fin.last _) {T : G.V → ZMod 2} (hsupp : ∀ v, T v ≠ 0 → v ∈ U) :
    G.Realizable U T := by
  rw [eq_sum_pairs T r]
  refine realizable_add (realizable_smul (realizable_single_rough hr hrough) _) (realizable_sum _ _ fun v _ => ?_)
  by_cases hv : T v = 0
  · rw [hv, zero_smul]
    exact realizable_zero U
  · exact realizable_smul (realizable_pair_of_reach (hU r hr v (hsupp v hv))) _

end S3Geom

end QECML
