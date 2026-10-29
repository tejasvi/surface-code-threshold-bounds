import QECD1.TypeFromCov3

/-!
# Corrections inside connected regions (towards the validity of the 3D decoder)

The 3D analogue of the 2D `S3/Connectivity`. `Realizable3 U S`: `S` is the syndrome of an edge set lying inside the
check set `U` (a half-edge lies inside `U` iff its check does). If `U` is connected, every syndrome supported in `U`
with even total parity is realizable (`realizable_of_even`); if `U` also contains a check of a rough side (`y = 0` or
`y = h`), every syndrome supported in `U` is realizable (`realizable_of_rough`). These are the two cases in which the
decoder resolves a component.
-/

open Finset

namespace QECD1

variable {T w h : ℕ}

/-- Two checks are adjacent if a bulk edge joins them. -/
def adj3 (u v : PVert3 T w h) : Prop := ∃ e : PEdge3 T w h, e.ends = {u, v} ∧ u ≠ v

theorem adj3_symm {u v : PVert3 T w h} (huv : adj3 u v) : adj3 v u := by
  obtain ⟨e, he, hne⟩ := huv
  exact ⟨e, by rw [he, Finset.pair_comm], hne.symm⟩

/-- A step of a path inside `U`. -/
def stepU3 (U : Set (PVert3 T w h)) (a b : PVert3 T w h) : Prop := a ∈ U ∧ b ∈ U ∧ adj3 a b

/-- `U` is connected: any two of its checks are joined by a path of adjacent checks of `U`. -/
def Conn3 (U : Set (PVert3 T w h)) : Prop := ∀ u ∈ U, ∀ v ∈ U, Relation.ReflTransGen (stepU3 U) u v

/-- The edge set `X` lies inside `U`: every check of every edge of `X` is in `U`. -/
def Inside3 (U : Set (PVert3 T w h)) (X : PEdge3 T w h → ZMod 2) : Prop := ∀ e, X e ≠ 0 → ∀ v ∈ e.ends, v ∈ U

/-- `S` is the syndrome of an edge set inside `U`. -/
def Realizable3 (U : Set (PVert3 T w h)) (S : PVert3 T w h → ZMod 2) : Prop := ∃ X, Inside3 U X ∧ psyn3 X = S

theorem psyn3_zero : psyn3 (0 : PEdge3 T w h → ZMod 2) = 0 := by
  funext v
  simp [psyn3]

theorem realizable_zero (U : Set (PVert3 T w h)) : Realizable3 U 0 :=
  ⟨0, fun _ h => absurd rfl h, psyn3_zero⟩

theorem realizable_add {U : Set (PVert3 T w h)} {S1 S2 : PVert3 T w h → ZMod 2} (h1 : Realizable3 U S1)
    (h2 : Realizable3 U S2) : Realizable3 U (S1 + S2) := by
  obtain ⟨X1, hi1, hs1⟩ := h1
  obtain ⟨X2, hi2, hs2⟩ := h2
  refine ⟨X1 + X2, fun e he v hv => ?_, by rw [psyn3_add, hs1, hs2]⟩
  by_cases hx : X1 e = 0
  · have h2' : X2 e ≠ 0 := by simpa [hx] using he
    exact hi2 e h2' v hv
  · exact hi1 e hx v hv

theorem realizable_smul {U : Set (PVert3 T w h)} {S : PVert3 T w h → ZMod 2} (hS : Realizable3 U S) (a : ZMod 2) :
    Realizable3 U (a • S) := by
  rcases zmod2_cases a with rfl | rfl
  · simpa using realizable_zero U
  · simpa using hS

theorem realizable_sum {U : Set (PVert3 T w h)} {ι : Type} (s : Finset ι) (S : ι → PVert3 T w h → ZMod 2)
    (hS : ∀ i ∈ s, Realizable3 U (S i)) : Realizable3 U (∑ i ∈ s, S i) :=
  Finset.sum_induction S (Realizable3 U) (fun _ _ ha hb => realizable_add ha hb) (realizable_zero U) hS

theorem psyn3_single (e : PEdge3 T w h) :
    psyn3 (Pi.single e 1) = fun v => if v ∈ e.ends then 1 else 0 := by
  funext v
  unfold psyn3
  by_cases hv : v ∈ e.ends
  · rw [if_pos hv, Finset.sum_eq_single e]
    · simp
    · intro f _ hfe
      simp [hfe]
    · intro he
      exact (he (Finset.mem_filter.2 ⟨Finset.mem_univ e, hv⟩)).elim
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun f hf => ?_
    have hfe : f ≠ e := fun h => hv (h ▸ (Finset.mem_filter.1 hf).2)
    simp [hfe]

/-- One bulk edge inside `U` realizes the pair of its ends. -/
theorem realizable_pair_of_adj {U : Set (PVert3 T w h)} {u v : PVert3 T w h} (hu : u ∈ U) (hv : v ∈ U)
    (huv : adj3 u v) : Realizable3 U (Pi.single u 1 + Pi.single v 1) := by
  obtain ⟨e, he, hne⟩ := huv
  refine ⟨Pi.single e 1, fun f hf x hx => ?_, ?_⟩
  · have hfe : f = e := by
      by_contra hfe
      simp [hfe] at hf
    subst hfe
    rw [he, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  · rw [psyn3_single, he]
    funext x
    simp only [Finset.mem_insert, Finset.mem_singleton, Pi.add_apply, Pi.single_apply]
    by_cases h1 : x = u <;> by_cases h2 : x = v <;> simp_all

/-- A path inside `U` realizes the pair of its ends. -/
theorem realizable_pair_of_reach {U : Set (PVert3 T w h)} {u v : PVert3 T w h}
    (huv : Relation.ReflTransGen (stepU3 U) u v) : Realizable3 U (Pi.single u 1 + Pi.single v 1) := by
  induction huv with
  | refl =>
    have hz : (Pi.single u 1 + Pi.single u 1 : PVert3 T w h → ZMod 2) = 0 := by
      funext x
      exact CharTwo.add_self_eq_zero _
    rw [hz]
    exact realizable_zero U
  | @tail b c _ hstep ih =>
    obtain ⟨hb, hc, hadj⟩ := hstep
    have h2 := realizable_add ih (realizable_pair_of_adj hb hc hadj)
    have hff : ∀ f : PVert3 T w h → ZMod 2, f + f = 0 := fun f => funext fun x => CharTwo.add_self_eq_zero (f x)
    have hid : (Pi.single u 1 + Pi.single c 1 : PVert3 T w h → ZMod 2) =
        Pi.single u 1 + Pi.single b 1 + (Pi.single b 1 + Pi.single c 1) := by
      rw [add_assoc, ← add_assoc (Pi.single b 1), hff, zero_add]
    rw [hid]
    exact h2

theorem eq_sum_pairs (S : PVert3 T w h → ZMod 2) (u0 : PVert3 T w h) :
    S = (∑ v, S v) • Pi.single u0 1 + ∑ v, S v • (Pi.single u0 1 + Pi.single v 1) := by
  funext x
  have h1 : (∑ v, S v • (Pi.single u0 1 + Pi.single v 1 : PVert3 T w h → ZMod 2)) x =
      (∑ v, S v) * (Pi.single u0 1 : PVert3 T w h → ZMod 2) x + S x := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    congr 1
    simp [Pi.single_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- In a connected region, every syndrome supported in it with even parity is realizable. -/
theorem realizable_of_even {U : Set (PVert3 T w h)} (hU : Conn3 U) {S : PVert3 T w h → ZMod 2}
    (hsupp : ∀ v, S v ≠ 0 → v ∈ U) (heven : ∑ v, S v = 0) : Realizable3 U S := by
  by_cases hne : ∃ u0, u0 ∈ U
  · obtain ⟨u0, hu0⟩ := hne
    rw [eq_sum_pairs S u0, heven, zero_smul, zero_add]
    refine realizable_sum _ _ fun v _ => ?_
    by_cases hv : S v = 0
    · rw [hv, zero_smul]
      exact realizable_zero U
    · exact realizable_smul (realizable_pair_of_reach (hU u0 hu0 v (hsupp v hv))) _
  · have hS : S = 0 := funext fun v => by
      by_contra hv
      exact hne ⟨v, hsupp v hv⟩
    rw [hS]
    exact realizable_zero U

/-- A check of a rough side inside `U` realizes itself through its half-edge. -/
theorem realizable_single_rough {U : Set (PVert3 T w h)} {r : PVert3 T w h} (hr : r ∈ U)
    (hrough : r.2.2 = 0 ∨ r.2.2 = Fin.last h) : Realizable3 U (Pi.single r 1) := by
  obtain ⟨rt, rx, ry⟩ := r
  rcases hrough with hy | hy <;> simp only at hy <;> subst hy
  · refine ⟨Pi.single (PEdge3.bot rt rx) 1, fun f hf x hx => ?_, ?_⟩
    · have hfe : f = PEdge3.bot rt rx := by
        by_contra hfe
        simp [hfe] at hf
      subst hfe
      simp only [PEdge3.ends, Finset.mem_singleton] at hx
      rw [hx]
      exact hr
    · rw [psyn3_single]
      funext x
      simp [PEdge3.ends, Pi.single_apply]
  · refine ⟨Pi.single (PEdge3.top rt rx) 1, fun f hf x hx => ?_, ?_⟩
    · have hfe : f = PEdge3.top rt rx := by
        by_contra hfe
        simp [hfe] at hf
      subst hfe
      simp only [PEdge3.ends, Finset.mem_singleton] at hx
      rw [hx]
      exact hr
    · rw [psyn3_single]
      funext x
      simp [PEdge3.ends, Pi.single_apply]

/-- In a connected region containing a check of a rough side, every syndrome supported in it is realizable. -/
theorem realizable_of_rough {U : Set (PVert3 T w h)} (hU : Conn3 U) {r : PVert3 T w h} (hr : r ∈ U)
    (hrough : r.2.2 = 0 ∨ r.2.2 = Fin.last h) {S : PVert3 T w h → ZMod 2} (hsupp : ∀ v, S v ≠ 0 → v ∈ U) :
    Realizable3 U S := by
  rw [eq_sum_pairs S r]
  refine realizable_add (realizable_smul (realizable_single_rough hr hrough) _) (realizable_sum _ _ fun v _ => ?_)
  by_cases hv : S v = 0
  · rw [hv, zero_smul]
    exact realizable_zero U
  · exact realizable_smul (realizable_pair_of_reach (hU r hr v (hsupp v hv))) _

end QECD1
