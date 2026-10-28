import QEC.Count.RotGeom
import QEC.Count.IID

/-!
# The rotated surface code (one error sector) and its region form

The rotated surface code of odd distance `d`, Z errors at code capacity:
* data qubits `(x, y) ∈ [0, d)²`;
* X checks at the plaquette positions `(i, j)` with `i + j` even, `0 ≤ i ≤ d - 2` and `-1 ≤ j ≤ d - 1`: the bulk
  weight-4 plaquettes (`0 ≤ j ≤ d - 2`) and the weight-2 checks of the boundary rows `j = -1` and `j = d - 1`; the
  qubits of a check are the corners of its plaquette (`inCheck`);
* the syndrome of a set `E` of flipped qubits: the X checks containing an odd number of them (`rotSyn`);
* the logical class: the parity of the flips on the column `x = 0` (the support of a logical X operator;
  `rotCls`); a correction fails when its class differs from the error's;
* minimum-weight decoding with uniform weights; `PfailRot d p`: every qubit flips independently with probability `p`,
  and some minimum-weight correction fails. `PfailRotML`: the least failure probability of a decoder from the
  syndrome to the class.

`PfailRot_eq`: the qubits are the edges of the region code `rotEdges d` (`RotGeom.lean`): the qubit `(x, y)` joins
the images `((i + j)/2, (i - j)/2)` of the two plaquette positions `(i, j)` around it of the right parity
(`(x - 1, y - 1)` and `(x, y)` if `x + y` is even, `(x, y - 1)` and `(x - 1, y)` if odd), a position with `i = -1` or
`i = d - 1` being an outer point. Syndromes and classes correspond, so the two failure probabilities are equal.
-/

namespace QEC

open Finset

variable (d : ℕ)

/-- The X checks of the rotated surface code of distance `d` (plaquette positions). -/
def rotXCh : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) (d - 2)) ×ˢ (Finset.Icc (-1 : ℤ) (d - 1))).filter (fun c => Even (c.1 + c.2))

/-- The qubit `q` is a corner of the plaquette at `c`. -/
def inCheck (q : Fin d × Fin d) (c : ℤ × ℤ) : Prop :=
  ((q.1 : ℤ) = c.1 ∨ (q.1 : ℤ) = c.1 + 1) ∧ ((q.2 : ℤ) = c.2 ∨ (q.2 : ℤ) = c.2 + 1)

instance (q : Fin d × Fin d) (c : ℤ × ℤ) : Decidable (inCheck d q c) := by unfold inCheck; infer_instance

/-- The syndrome: the X checks with an odd number of flipped qubits. -/
def rotSyn (E : Finset (Fin d × Fin d)) : Finset (ℤ × ℤ) :=
  (rotXCh d).filter (fun c => Odd #(E.filter (fun q => inCheck d q c)))

/-- The logical class: the parity of the flips on the column `x = 0`. -/
def rotCls (E : Finset (Fin d × Fin d)) : Prop := Odd #(E.filter (fun q => (q.1 : ℕ) = 0))

instance (E : Finset (Fin d × Fin d)) : Decidable (rotCls d E) := by unfold rotCls; infer_instance

/-- A minimum-weight correction (uniform weights). -/
def IsMinCorrRot (E C : Finset (Fin d × Fin d)) : Prop :=
  rotSyn d C = rotSyn d E ∧ ∀ C' : Finset (Fin d × Fin d), rotSyn d C' = rotSyn d E → #C ≤ #C'

/-- The correction `C` fails for the error `E`. -/
def FailsRot (E C : Finset (Fin d × Fin d)) : Prop := ¬ (rotCls d C ↔ rotCls d E)

/-- The probability that some minimum-weight correction fails. -/
noncomputable def PfailRot (p : ℝ) : ℝ :=
  PrIID (univ : Finset (Fin d × Fin d)) p (fun E => ∃ C, IsMinCorrRot d E C ∧ FailsRot d E C)

/-- The optimal (maximum-likelihood) failure probability. -/
noncomputable def PfailRotML (p : ℝ) : ℝ :=
  ⨅ dec : Finset (ℤ × ℤ) → Bool,
    PrIID (univ : Finset (Fin d × Fin d)) p (fun E => dec (rotSyn d E) ≠ decide (rotCls d E))

section Helpers

variable {d}

namespace RotLayout

open QECComp

/-- The lattice point of a vertex. -/
def pt : RVx (RChk d) (ROut d) → ℤ × ℤ
  | .chk v => v.1
  | .out w => w.1

/-- The plaquette coordinate `i = U + V` of a vertex. -/
def iOf (a : RVx (RChk d) (ROut d)) : ℤ := (pt a).1 + (pt a).2

/-- The plaquette coordinate `j = U - V` of a vertex. -/
def jOf (a : RVx (RChk d) (ROut d)) : ℤ := (pt a).1 - (pt a).2

theorem mem_rotChk {x : ℤ × ℤ} : x ∈ rotChk d ↔
    0 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d - 2 ∧ -1 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ d - 1 := by
  simp only [rotChk, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, h⟩

theorem mem_rotOut (hd : 1 ≤ d) {x : ℤ × ℤ} : x ∈ rotOut d ↔
    (x.1 + x.2 = -1 ∨ x.1 + x.2 = d - 1) ∧ -1 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ d - 1 := by
  simp only [rotOut, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, h⟩

theorem out_cond (w : ROut d) :
    (w.1.1 + w.1.2 = -1 ∨ w.1.1 + w.1.2 = d - 1) ∧ -1 ≤ w.1.1 - w.1.2 ∧ w.1.1 - w.1.2 ≤ d - 1 := by
  have := w.2
  simp only [rotOut, Finset.mem_filter] at this
  exact this.2

theorem chk_cond (v : RChk d) :
    0 ≤ v.1.1 + v.1.2 ∧ v.1.1 + v.1.2 ≤ d - 2 ∧ -1 ≤ v.1.1 - v.1.2 ∧ v.1.1 - v.1.2 ≤ d - 1 :=
  mem_rotChk.mp v.2

theorem iOf_chk (v : RChk d) : iOf (RVx.chk v : RVx (RChk d) (ROut d)) = v.1.1 + v.1.2 := rfl
theorem jOf_chk (v : RChk d) : jOf (RVx.chk v : RVx (RChk d) (ROut d)) = v.1.1 - v.1.2 := rfl
theorem iOf_out (w : ROut d) : iOf (RVx.out w : RVx (RChk d) (ROut d)) = w.1.1 + w.1.2 := rfl
theorem jOf_out (w : ROut d) : jOf (RVx.out w : RVx (RChk d) (ROut d)) = w.1.1 - w.1.2 := rfl

/-- The plaquette coordinates of every vertex lie in `[-1, d - 1]` and have an even sum. -/
theorem ij_range (a : RVx (RChk d) (ROut d)) :
    -1 ≤ iOf a ∧ iOf a ≤ d - 1 ∧ -1 ≤ jOf a ∧ jOf a ≤ d - 1 ∧ Even (iOf a + jOf a) := by
  cases a with
  | chk v =>
    have := chk_cond v
    simp only [iOf_chk, jOf_chk]
    exact ⟨by omega, by omega, by omega, by omega, ⟨v.1.1, by ring⟩⟩
  | out w =>
    have := out_cond w
    simp only [iOf_out, jOf_out]
    exact ⟨by omega, by omega, by omega, by omega, ⟨w.1.1, by ring⟩⟩

/-- A check has `0 ≤ i ≤ d - 2`, an outer point `i = -1` or `i = d - 1`. -/
theorem iOf_chk_range (v : RChk d) :
    0 ≤ iOf (RVx.chk v : RVx (RChk d) (ROut d)) ∧ iOf (RVx.chk v : RVx (RChk d) (ROut d)) ≤ d - 2 := by
  have := chk_cond v
  simp only [iOf_chk]
  exact ⟨this.1, this.2.1⟩

theorem iOf_out_range (w : ROut d) :
    iOf (RVx.out w : RVx (RChk d) (ROut d)) = -1 ∨ iOf (RVx.out w : RVx (RChk d) (ROut d)) = d - 1 := by
  have := out_cond w
  simp only [iOf_out]
  exact this.1

/-- A vertex is determined by its plaquette coordinates. -/
theorem eq_of_ij {a b : RVx (RChk d) (ROut d)} (hi : iOf a = iOf b) (hj : jOf a = jOf b) : a = b := by
  have hpt : pt a = pt b := by
    simp only [iOf, jOf] at hi hj
    ext <;> omega
  cases a with
  | chk v =>
    cases b with
    | chk v' => exact congrArg RVx.chk (Subtype.ext hpt)
    | out w' =>
      exfalso
      have h1 := iOf_chk_range v
      have h2 := iOf_out_range w'
      rw [hi] at h1
      omega
  | out w =>
    cases b with
    | chk v' =>
      exfalso
      have h1 := iOf_chk_range v'
      have h2 := iOf_out_range w
      rw [hi] at h2
      omega
    | out w' => exact congrArg RVx.out (Subtype.ext hpt)

/-- The vertex at plaquette coordinates `(i, j)` (`dflt` if there is none). -/
def ptOf (dflt : RVx (RChk d) (ROut d)) (i j : ℤ) : RVx (RChk d) (ROut d) :=
  if h : ((i + j) / 2, (i - j) / 2) ∈ rotChk d then RVx.chk ⟨_, h⟩
  else if h' : ((i + j) / 2, (i - j) / 2) ∈ rotOut d then RVx.out ⟨_, h'⟩ else dflt

/-- At valid plaquette coordinates, `ptOf` is the vertex with these coordinates. -/
theorem ptOf_ij (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) {i j : ℤ} (hij : Even (i + j))
    (hi : -1 ≤ i ∧ i ≤ d - 1) (hj : -1 ≤ j ∧ j ≤ d - 1) :
    iOf (ptOf dflt i j) = i ∧ jOf (ptOf dflt i j) = j := by
  obtain ⟨k, hk⟩ := hij
  have e1 : (i + j) / 2 = k := by omega
  have e2 : (i - j) / 2 = k - j := by omega
  unfold ptOf
  split_ifs with h h'
  · simp only [iOf_chk, jOf_chk]
    rw [e1, e2]
    constructor <;> omega
  · simp only [iOf_out, jOf_out]
    rw [e1, e2]
    constructor <;> omega
  · exfalso
    rw [e1, e2] at h h'
    rw [mem_rotChk] at h
    rw [mem_rotOut hd] at h'
    simp only at h h'
    omega

/-- `ptOf` at the plaquette coordinates of a vertex is the vertex. -/
theorem ptOf_pos (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) (a : RVx (RChk d) (ROut d)) :
    ptOf dflt (iOf a) (jOf a) = a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ij_range a
  obtain ⟨e1, e2⟩ := ptOf_ij hd dflt h5 ⟨h1, h2⟩ ⟨h3, h4⟩
  exact eq_of_ij e1 e2

/-- The edge of a qubit: the vertices at the two plaquette positions around it of even coordinate sum. -/
def edgeOf (dflt : RVx (RChk d) (ROut d)) (q : Fin d × Fin d) : Sym2 (RVx (RChk d) (ROut d)) :=
  if Even ((q.1 : ℤ) + (q.2 : ℤ)) then s(ptOf dflt ((q.1 : ℤ) - 1) ((q.2 : ℤ) - 1), ptOf dflt (q.1 : ℤ) (q.2 : ℤ))
  else s(ptOf dflt (q.1 : ℤ) ((q.2 : ℤ) - 1), ptOf dflt ((q.1 : ℤ) - 1) (q.2 : ℤ))

/-- The vertices of the edge of `q` are those whose plaquette coordinates are corners around `q`. -/
theorem mem_edgeOf (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) (q : Fin d × Fin d) (a : RVx (RChk d) (ROut d)) :
    a ∈ edgeOf dflt q ↔
      (iOf a = (q.1 : ℤ) - 1 ∨ iOf a = (q.1 : ℤ)) ∧ (jOf a = (q.2 : ℤ) - 1 ∨ jOf a = (q.2 : ℤ)) := by
  have hx : (q.1 : ℤ) < d := by exact_mod_cast q.1.2
  have hy : (q.2 : ℤ) < d := by exact_mod_cast q.2.2
  have hx0 : (0 : ℤ) ≤ (q.1 : ℤ) := by positivity
  have hy0 : (0 : ℤ) ≤ (q.2 : ℤ) := by positivity
  have hpar := (ij_range a).2.2.2.2
  rw [Int.even_iff] at hpar
  unfold edgeOf
  split_ifs with hev
  · rw [Int.even_iff] at hev
    have e1 := ptOf_ij hd dflt (i := (q.1 : ℤ) - 1) (j := (q.2 : ℤ) - 1) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have e2 := ptOf_ij hd dflt (i := (q.1 : ℤ)) (j := (q.2 : ℤ)) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    rw [Sym2.mem_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inl e1.1, Or.inl e1.2⟩
      · exact ⟨Or.inr e2.1, Or.inr e2.2⟩
    · rintro ⟨hi | hi, hj | hj⟩
      · left; rw [← ptOf_pos hd dflt a, hi, hj]
      · exfalso; rw [hi, hj] at hpar; omega
      · exfalso; rw [hi, hj] at hpar; omega
      · right; rw [← ptOf_pos hd dflt a, hi, hj]
  · rw [Int.even_iff] at hev
    have e1 := ptOf_ij hd dflt (i := (q.1 : ℤ)) (j := (q.2 : ℤ) - 1) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have e2 := ptOf_ij hd dflt (i := (q.1 : ℤ) - 1) (j := (q.2 : ℤ)) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    rw [Sym2.mem_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inr e1.1, Or.inl e1.2⟩
      · exact ⟨Or.inl e2.1, Or.inr e2.2⟩
    · rintro ⟨hi | hi, hj | hj⟩
      · exfalso; rw [hi, hj] at hpar; omega
      · right; rw [← ptOf_pos hd dflt a, hi, hj]
      · left; rw [← ptOf_pos hd dflt a, hi, hj]
      · exfalso; rw [hi, hj] at hpar; omega

/-- The larger `i` of the two ends of an edge. -/
def imax : Sym2 (RVx (RChk d) (ROut d)) → ℤ :=
  Sym2.lift ⟨fun a b => max (iOf a) (iOf b), fun _ _ => max_comm _ _⟩

/-- The larger `j` of the two ends of an edge. -/
def jmax : Sym2 (RVx (RChk d) (ROut d)) → ℤ :=
  Sym2.lift ⟨fun a b => max (jOf a) (jOf b), fun _ _ => max_comm _ _⟩

/-- The qubit of an edge is recovered as `(imax, jmax)`. -/
theorem max_edgeOf (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) (q : Fin d × Fin d) :
    imax (edgeOf dflt q) = (q.1 : ℤ) ∧ jmax (edgeOf dflt q) = (q.2 : ℤ) := by
  have hx : (q.1 : ℤ) < d := by exact_mod_cast q.1.2
  have hy : (q.2 : ℤ) < d := by exact_mod_cast q.2.2
  have hx0 : (0 : ℤ) ≤ (q.1 : ℤ) := by positivity
  have hy0 : (0 : ℤ) ≤ (q.2 : ℤ) := by positivity
  unfold edgeOf
  split_ifs with hev
  · rw [Int.even_iff] at hev
    have e1 := ptOf_ij hd dflt (i := (q.1 : ℤ) - 1) (j := (q.2 : ℤ) - 1) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have e2 := ptOf_ij hd dflt (i := (q.1 : ℤ)) (j := (q.2 : ℤ)) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    simp only [imax, jmax, Sym2.lift_mk]
    rw [e1.1, e1.2, e2.1, e2.2]
    constructor <;> omega
  · rw [Int.even_iff] at hev
    have e1 := ptOf_ij hd dflt (i := (q.1 : ℤ)) (j := (q.2 : ℤ) - 1) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have e2 := ptOf_ij hd dflt (i := (q.1 : ℤ) - 1) (j := (q.2 : ℤ)) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    simp only [imax, jmax, Sym2.lift_mk]
    rw [e1.1, e1.2, e2.1, e2.2]
    constructor <;> omega

theorem edgeOf_injective (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) : Function.Injective (edgeOf dflt) := by
  intro q q' h
  have h1 := max_edgeOf hd dflt q
  have h2 := max_edgeOf hd dflt q'
  rw [h] at h1
  have ex : (q.1 : ℤ) = (q'.1 : ℤ) := h1.1.symm.trans h2.1
  have ey : (q.2 : ℤ) = (q'.2 : ℤ) := h1.2.symm.trans h2.2
  exact Prod.ext (Fin.ext (by exact_mod_cast ex)) (Fin.ext (by exact_mod_cast ey))

theorem l1_posR (a b : RVx (RChk d) (ROut d)) :
    l1 (posR a) (posR b) = ((pt a).1 - (pt b).1).natAbs + ((pt a).2 - (pt b).2).natAbs := by
  cases a <;> cases b <;> simp [posR, l1, pt]

/-- Neighbouring vertices differ by `±1` in both plaquette coordinates, and conversely. -/
theorem l1_eq_one_iff (a b : RVx (RChk d) (ROut d)) :
    l1 (posR a) (posR b) = 1 ↔
      (iOf a - iOf b = 1 ∨ iOf a - iOf b = -1) ∧ (jOf a - jOf b = 1 ∨ jOf a - jOf b = -1) := by
  rw [l1_posR]
  simp only [iOf, jOf]
  constructor
  · intro h
    rcases Int.natAbs_eq ((pt a).1 - (pt b).1) with h1 | h1 <;>
      rcases Int.natAbs_eq ((pt a).2 - (pt b).2) with h2 | h2 <;> omega
  · rintro ⟨h1 | h1, h2 | h2⟩
    · rw [show (pt a).1 - (pt b).1 = 1 by omega, show (pt a).2 - (pt b).2 = 0 by omega]; rfl
    · rw [show (pt a).1 - (pt b).1 = 0 by omega, show (pt a).2 - (pt b).2 = 1 by omega]; rfl
    · rw [show (pt a).1 - (pt b).1 = 0 by omega, show (pt a).2 - (pt b).2 = -1 by omega]; rfl
    · rw [show (pt a).1 - (pt b).1 = -1 by omega, show (pt a).2 - (pt b).2 = 0 by omega]; rfl

theorem mem_rotEdges {e : Sym2 (RVx (RChk d) (ROut d))} :
    e ∈ rotEdges d ↔ ∃ a b, RotAdj a b ∧ s(a, b) = e := by
  simp only [rotEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Prod.exists]

theorem rotAdj_iff (a b : RVx (RChk d) (ROut d)) :
    RotAdj a b ↔ ¬ ((∃ w, a = RVx.out w) ∧ (∃ w, b = RVx.out w)) ∧ l1 (posR a) (posR b) = 1 := by
  cases a <;> cases b <;> simp [RotAdj]

theorem edgeOf_mem (hd : 2 ≤ d) (dflt : RVx (RChk d) (ROut d)) (q : Fin d × Fin d) :
    edgeOf dflt q ∈ rotEdges d := by
  have hd1 : 1 ≤ d := by omega
  have hx : (q.1 : ℤ) < d := by exact_mod_cast q.1.2
  have hy : (q.2 : ℤ) < d := by exact_mod_cast q.2.2
  have hx0 : (0 : ℤ) ≤ (q.1 : ℤ) := by positivity
  have hy0 : (0 : ℤ) ≤ (q.2 : ℤ) := by positivity
  rw [mem_rotEdges]
  -- two vertices with `|Δi| = |Δj| = 1` whose `i` are `x - 1` and `x` are never both outer points
  have key : ∀ a b : RVx (RChk d) (ROut d), iOf a = (q.1 : ℤ) - 1 → iOf b = (q.1 : ℤ) →
      (jOf a - jOf b = 1 ∨ jOf a - jOf b = -1) → RotAdj a b := by
    intro a b ha hb hj
    rw [rotAdj_iff, l1_eq_one_iff]
    refine ⟨?_, Or.inr (by omega), hj⟩
    rintro ⟨⟨w, rfl⟩, ⟨w', rfl⟩⟩
    have h1 := iOf_out_range w
    have h2 := iOf_out_range w'
    omega
  unfold edgeOf
  split_ifs with hev
  · rw [Int.even_iff] at hev
    have e1 := ptOf_ij hd1 dflt (i := (q.1 : ℤ) - 1) (j := (q.2 : ℤ) - 1) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have e2 := ptOf_ij hd1 dflt (i := (q.1 : ℤ)) (j := (q.2 : ℤ)) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    exact ⟨_, _, key _ _ e1.1 e2.1 (Or.inr (by omega)), rfl⟩
  · rw [Int.even_iff] at hev
    have e1 := ptOf_ij hd1 dflt (i := (q.1 : ℤ)) (j := (q.2 : ℤ) - 1) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have e2 := ptOf_ij hd1 dflt (i := (q.1 : ℤ) - 1) (j := (q.2 : ℤ)) (by rw [Int.even_iff]; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    refine ⟨_, _, ?_, Sym2.eq_swap⟩
    exact key _ _ e2.1 e1.1 (Or.inl (by omega))

/-- Every edge of the region is the edge of a qubit. -/
theorem exists_edgeOf (hd : 2 ≤ d) (dflt : RVx (RChk d) (ROut d)) {e : Sym2 (RVx (RChk d) (ROut d))}
    (he : e ∈ rotEdges d) : ∃ q, edgeOf dflt q = e := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨a, b, hab, rfl⟩ := mem_rotEdges.mp he
  rw [rotAdj_iff, l1_eq_one_iff] at hab
  obtain ⟨-, hi, hj⟩ := hab
  obtain ⟨ia1, ia2, ja1, ja2, pa⟩ := ij_range a
  obtain ⟨ib1, ib2, jb1, jb2, pb⟩ := ij_range b
  rw [Int.even_iff] at pa pb
  set x := max (iOf a) (iOf b) with hxdef
  set y := max (jOf a) (jOf b) with hydef
  have hx0 : 0 ≤ x := by omega
  have hxd : x < d := by omega
  have hy0 : 0 ≤ y := by omega
  have hyd : y < d := by omega
  refine ⟨(⟨x.toNat, by omega⟩, ⟨y.toNat, by omega⟩), ?_⟩
  have cx : ((⟨x.toNat, by omega⟩ : Fin d) : ℤ) = x := by simp; omega
  have cy : ((⟨y.toNat, by omega⟩ : Fin d) : ℤ) = y := by simp; omega
  apply Sym2.ext
  intro z
  rw [mem_edgeOf hd1, Sym2.mem_iff]
  simp only [cx, cy]
  constructor
  · rintro ⟨hzi, hzj⟩
    obtain ⟨-, -, -, -, pz⟩ := ij_range z
    rw [Int.even_iff] at pz
    by_cases hza : iOf z = iOf a
    · left; exact eq_of_ij hza (by omega)
    · right; exact eq_of_ij (by omega) (by omega)
  · rintro (rfl | rfl)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩

/-- The edge map as an embedding. -/
def edgeEmb (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) : Fin d × Fin d ↪ Sym2 (RVx (RChk d) (ROut d)) :=
  ⟨edgeOf dflt, edgeOf_injective hd dflt⟩

theorem image_edgeOf (hd : 2 ≤ d) (dflt : RVx (RChk d) (ROut d)) :
    (univ : Finset (Fin d × Fin d)).map (edgeEmb (by omega) dflt) = rotEdges d := by
  ext e
  simp only [Finset.mem_map, Finset.mem_univ, true_and, edgeEmb, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨q, rfl⟩; exact edgeOf_mem hd dflt q
  · intro he; exact exists_edgeOf hd dflt he

theorem vdeg_map (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) (E : Finset (Fin d × Fin d))
    (z : RVx (RChk d) (ROut d)) :
    vdeg (E.map (edgeEmb hd dflt)) z = #(E.filter (fun q => z ∈ edgeOf dflt q)) := by
  unfold vdeg
  rw [Finset.filter_map, Finset.card_map]
  rfl

/-- The plaquette position of a check. -/
def cpos (v : RChk d) : ℤ × ℤ := (iOf (RVx.chk v : RVx (RChk d) (ROut d)), jOf (RVx.chk v : RVx (RChk d) (ROut d)))

theorem chk_mem_edgeOf (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) (q : Fin d × Fin d) (v : RChk d) :
    (RVx.chk v : RVx (RChk d) (ROut d)) ∈ edgeOf dflt q ↔ inCheck d q (cpos v) := by
  rw [mem_edgeOf hd, cpos, inCheck]
  simp only
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩

theorem cpos_mem (v : RChk d) : cpos v ∈ rotXCh d := by
  have := chk_cond v
  simp only [cpos, iOf_chk, jOf_chk, rotXCh, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ⟨v.1.1, by ring⟩⟩

theorem cpos_injective : Function.Injective (cpos (d := d)) := by
  intro v v' h
  simp only [cpos, Prod.mk.injEq] at h
  have := eq_of_ij h.1 h.2
  exact RVx.chk.inj this

theorem exists_cpos {c : ℤ × ℤ} (hc : c ∈ rotXCh d) : ∃ v : RChk d, cpos v = c := by
  simp only [rotXCh, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hc
  obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨k, hk⟩⟩ := hc
  have hmem : (k, k - c.2) ∈ rotChk d := by
    rw [mem_rotChk]
    simp only
    omega
  refine ⟨⟨(k, k - c.2), hmem⟩, ?_⟩
  simp only [cpos, iOf_chk, jOf_chk]
  ext <;> simp <;> omega

theorem rbd_map (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) (E : Finset (Fin d × Fin d)) (v : RChk d) :
    v ∈ rbd (E.map (edgeEmb hd dflt)) ↔ cpos v ∈ rotSyn d E := by
  simp only [rbd, Finset.mem_filter, Finset.mem_univ, true_and, rotSyn]
  rw [vdeg_map hd]
  have hf : E.filter (fun q => (RVx.chk v : RVx (RChk d) (ROut d)) ∈ edgeOf dflt q) =
      E.filter (fun q => inCheck d q (cpos v)) :=
    Finset.filter_congr (fun q _ => chk_mem_edgeOf hd dflt q v)
  rw [hf]
  exact ⟨fun h => ⟨cpos_mem v, h⟩, fun h => h.2⟩

/-- Syndromes correspond. -/
theorem syn_iff (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) (C E : Finset (Fin d × Fin d)) :
    rotSyn d C = rotSyn d E ↔ rbd (C.map (edgeEmb hd dflt)) = rbd (E.map (edgeEmb hd dflt)) := by
  constructor
  · intro h
    ext v
    rw [rbd_map, rbd_map, h]
  · intro h
    ext c
    by_cases hc : c ∈ rotXCh d
    · obtain ⟨v, rfl⟩ := exists_cpos hc
      rw [← rbd_map hd dflt, ← rbd_map hd dflt, h]
    · simp only [rotSyn, Finset.mem_filter, hc, false_and]

/-- The side-1 outer points of the edge of `q`: there is one iff `q` is on the column `x = 0`. -/
theorem side1_iff (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) (q : Fin d × Fin d) :
    (∃ w : ROut d, rotSide w = true ∧ (RVx.out w : RVx (RChk d) (ROut d)) ∈ edgeOf dflt q) ↔
      (q.1 : ℕ) = 0 := by
  have hx : (q.1 : ℤ) < d := by exact_mod_cast q.1.2
  have hy : (q.2 : ℤ) < d := by exact_mod_cast q.2.2
  have hx0 : (0 : ℤ) ≤ (q.1 : ℤ) := by positivity
  have hy0 : (0 : ℤ) ≤ (q.2 : ℤ) := by positivity
  constructor
  · rintro ⟨w, hw, hmem⟩
    rw [mem_edgeOf hd] at hmem
    simp only [rotSide, decide_eq_true_eq] at hw
    rw [iOf_out] at hmem
    have : (q.1 : ℤ) = 0 := by omega
    exact_mod_cast this
  · intro hq0
    have hq : (q.1 : ℤ) = 0 := by exact_mod_cast hq0
    set j0 : ℤ := if Even (q.2 : ℤ) then (q.2 : ℤ) - 1 else (q.2 : ℤ) with hj0
    have hj0r : (j0 = (q.2 : ℤ) - 1 ∨ j0 = (q.2 : ℤ)) ∧ Even (-1 + j0) := by
      rw [hj0]
      split_ifs with he
      · rw [Int.even_iff] at he ⊢; exact ⟨Or.inl rfl, by omega⟩
      · rw [Int.even_iff] at he ⊢; exact ⟨Or.inr rfl, by omega⟩
    obtain ⟨e1, e2⟩ := ptOf_ij hd dflt (i := -1) (j := j0) hj0r.2 ⟨le_rfl, by omega⟩ ⟨by omega, by omega⟩
    have hmem : ptOf dflt (-1) j0 ∈ edgeOf dflt q := by
      rw [mem_edgeOf hd, e1, e2]
      exact ⟨Or.inl (by omega), hj0r.1⟩
    generalize ptOf dflt (-1) j0 = a at e1 e2 hmem
    cases a with
    | chk v => exfalso; have := iOf_chk_range v; omega
    | out w =>
      refine ⟨w, ?_, hmem⟩
      simp only [rotSide, decide_eq_true_eq]
      rw [iOf_out] at e1
      exact e1

/-- The edge of a qubit has at most one side-1 outer point. -/
theorem side1_unique (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) (q : Fin d × Fin d) {w w' : ROut d}
    (hw : rotSide w = true) (hw' : rotSide w' = true)
    (h1 : (RVx.out w : RVx (RChk d) (ROut d)) ∈ edgeOf dflt q)
    (h2 : (RVx.out w' : RVx (RChk d) (ROut d)) ∈ edgeOf dflt q) : w = w' := by
  rw [mem_edgeOf hd] at h1 h2
  simp only [rotSide, decide_eq_true_eq] at hw hw'
  have p1 := (ij_range (RVx.out w : RVx (RChk d) (ROut d))).2.2.2.2
  have p2 := (ij_range (RVx.out w' : RVx (RChk d) (ROut d))).2.2.2.2
  rw [Int.even_iff] at p1 p2
  rw [iOf_out] at h1 h2 p1 p2
  rw [jOf_out] at p1 p2
  have hij : iOf (RVx.out w : RVx (RChk d) (ROut d)) = iOf (RVx.out w' : RVx (RChk d) (ROut d)) := by
    rw [iOf_out, iOf_out]; omega
  have hjj : jOf (RVx.out w : RVx (RChk d) (ROut d)) = jOf (RVx.out w' : RVx (RChk d) (ROut d)) := by
    rw [jOf_out, jOf_out]
    rw [jOf_out] at h1 h2
    omega
  exact RVx.out.inj (eq_of_ij hij hjj)

theorem side1deg_map (hd : 1 ≤ d) (dflt : RVx (RChk d) (ROut d)) (E : Finset (Fin d × Fin d)) :
    side1deg rotSide (E.map (edgeEmb hd dflt)) = #(E.filter (fun q => (q.1 : ℕ) = 0)) := by
  unfold side1deg
  simp_rw [vdeg_map hd]
  rw [← Finset.card_biUnion]
  · congr 1
    ext q
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, hq, hmem⟩
      exact ⟨hq, (side1_iff hd dflt q).mp ⟨w, hw, hmem⟩⟩
    · rintro ⟨hq, h0⟩
      obtain ⟨w, hw, hmem⟩ := (side1_iff hd dflt q).mpr h0
      exact ⟨w, hw, hq, hmem⟩
  · intro w hw w' hw' hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw hw'
    rw [Function.onFun, Finset.disjoint_left]
    intro q hq hq'
    simp only [Finset.mem_filter] at hq hq'
    exact hne (side1_unique hd dflt q hw hw' hq.2 hq'.2)

end RotLayout

end Helpers

/-- **The rotated code is the region code `rotEdges d`.** -/
theorem PfailRot_eq (hd : 3 ≤ d) (hodd : Odd d) (p : ℝ) : PfailRot d p = PfailMWR (rotEdges d) rotSide p := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have h00 : ((0 : ℤ), (0 : ℤ)) ∈ rotChk d := by
    rw [RotLayout.mem_rotChk]; simp only; omega
  obtain ⟨dflt⟩ : Nonempty (RVx (RChk d) (ROut d)) := ⟨RVx.chk ⟨(0, 0), h00⟩⟩
  have himg : (univ : Finset (Fin d × Fin d)).map (RotLayout.edgeEmb hd1 dflt) = rotEdges d :=
    RotLayout.image_edgeOf hd2 dflt
  -- preimages of edge sets
  have map_sub : ∀ E : Finset (Fin d × Fin d), E.map (RotLayout.edgeEmb hd1 dflt) ⊆ rotEdges d := by
    intro E
    rw [← himg]
    exact Finset.map_subset_map.mpr (Finset.subset_univ E)
  have map_pre : ∀ E' ⊆ rotEdges d,
      ((univ : Finset (Fin d × Fin d)).filter (fun q => RotLayout.edgeEmb hd1 dflt q ∈ E')).map
        (RotLayout.edgeEmb hd1 dflt) = E' := by
    intro E' hE'
    ext e
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro he
      have : e ∈ (univ : Finset (Fin d × Fin d)).map (RotLayout.edgeEmb hd1 dflt) := by rw [himg]; exact hE' he
      obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp this
      exact ⟨q, he, rfl⟩
  have pre_map : ∀ E : Finset (Fin d × Fin d),
      (univ : Finset (Fin d × Fin d)).filter (fun q => RotLayout.edgeEmb hd1 dflt q ∈
        E.map (RotLayout.edgeEmb hd1 dflt)) = E := by
    intro E
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map']
  -- the events correspond
  have hfail : ∀ E C : Finset (Fin d × Fin d), FailsRot d E C ↔
      FailsR rotSide (E.map (RotLayout.edgeEmb hd1 dflt)) (C.map (RotLayout.edgeEmb hd1 dflt)) := by
    intro E C
    simp only [FailsRot, FailsR, rotCls, RotLayout.side1deg_map]
  have hA : ∀ E : Finset (Fin d × Fin d), (∃ C, IsMinCorrRot d E C ∧ FailsRot d E C) ↔
      (∃ C', IsMinCorrR (rotEdges d) (rbd (E.map (RotLayout.edgeEmb hd1 dflt))) C' ∧
        FailsR rotSide (E.map (RotLayout.edgeEmb hd1 dflt)) C') := by
    intro E
    constructor
    · rintro ⟨C, ⟨hsyn, hmin⟩, hfl⟩
      refine ⟨C.map (RotLayout.edgeEmb hd1 dflt), ⟨map_sub C, (RotLayout.syn_iff hd1 dflt C E).mp hsyn, ?_⟩,
        (hfail E C).mp hfl⟩
      intro C'' hC'' hbd
      rw [← map_pre C'' hC''] at hbd ⊢
      rw [Finset.card_map, Finset.card_map]
      exact hmin _ ((RotLayout.syn_iff hd1 dflt _ E).mpr hbd)
    · rintro ⟨C', ⟨hC', hbd, hmin⟩, hfl⟩
      have h1 := map_pre C' hC'
      refine ⟨(univ : Finset (Fin d × Fin d)).filter (fun q => RotLayout.edgeEmb hd1 dflt q ∈ C'),
        ⟨(RotLayout.syn_iff hd1 dflt _ E).mpr (by rw [h1]; exact hbd), ?_⟩, ?_⟩
      · intro C'' hsyn
        have := hmin (C''.map (RotLayout.edgeEmb hd1 dflt)) (map_sub C'')
          ((RotLayout.syn_iff hd1 dflt C'' E).mp hsyn)
        rw [← h1, Finset.card_map, Finset.card_map] at this
        exact this
      · rw [hfail, h1]; exact hfl
  unfold PfailRot PfailMWR PrIID
  apply Finset.sum_nbij' (fun E => E.map (RotLayout.edgeEmb hd1 dflt))
    (fun E' => (univ : Finset (Fin d × Fin d)).filter (fun q => RotLayout.edgeEmb hd1 dflt q ∈ E'))
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_powerset] at hE ⊢
    exact ⟨map_sub E, (hA E).mp hE.2⟩
  · intro E' hE'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hE' ⊢
    refine ⟨Finset.subset_univ _, (hA _).mpr ?_⟩
    rw [map_pre E' hE'.1]
    exact hE'.2
  · intro E _
    exact pre_map E
  · intro E' hE'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hE'
    exact map_pre E' hE'.1
  · intro E _
    rw [Finset.card_map, ← himg, ← Finset.map_sdiff, Finset.card_map]

/-- ML decoding is at least as good as any minimum-weight decoder. -/
theorem PfailRotML_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PfailRotML d p ≤ PfailRot d p := by
  classical
  -- a minimum-weight decoder with a syndrome-only tie rule (a chosen minimizer)
  let dec : Finset (ℤ × ℤ) → Bool := fun s =>
    if h : ∃ C : Finset (Fin d × Fin d), rotSyn d C = s ∧
        ∀ C' : Finset (Fin d × Fin d), rotSyn d C' = s → #C ≤ #C' then
      decide (rotCls d (Classical.choose h)) else false
  have hle : PfailRotML d p ≤
      PrIID (univ : Finset (Fin d × Fin d)) p (fun E => dec (rotSyn d E) ≠ decide (rotCls d E)) := by
    unfold PfailRotML
    exact ciInf_le ⟨0, by rintro _ ⟨dec', rfl⟩; exact PrIID_nonneg _ hp0 hp1 _⟩ dec
  refine le_trans hle (PrIID_mono _ hp0 hp1 ?_)
  intro E _ hne
  -- the syndrome of `E` has a minimizer: there are finitely many corrections, `E` among them
  have hex : ∃ C : Finset (Fin d × Fin d), rotSyn d C = rotSyn d E ∧
      ∀ C' : Finset (Fin d × Fin d), rotSyn d C' = rotSyn d E → #C ≤ #C' := by
    have hne' : ((univ : Finset (Finset (Fin d × Fin d))).filter (fun C => rotSyn d C = rotSyn d E)).Nonempty :=
      ⟨E, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image _ (fun C => #C) hne'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
    exact ⟨C, hC, fun C' hC' => hmin C' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC'⟩)⟩
  refine ⟨Classical.choose hex, Classical.choose_spec hex, ?_⟩
  have hdec : dec (rotSyn d E) = decide (rotCls d (Classical.choose hex)) := by
    simp [dec, hex]
  rw [hdec] at hne
  intro hiff
  exact hne (decide_eq_decide.mpr hiff)

/-- The number of qubits on the column `x = 0`, i.e. of side-1 half-edges. -/
theorem card_side1 (hd : 3 ≤ d) (hodd : Odd d) :
    #((rotEdges d).filter (fun e => ∃ w : ROut d, rotSide w = true ∧ RVx.out w ∈ e)) = d := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have h00 : ((0 : ℤ), (0 : ℤ)) ∈ rotChk d := by
    rw [RotLayout.mem_rotChk]; simp only; omega
  obtain ⟨dflt⟩ : Nonempty (RVx (RChk d) (ROut d)) := ⟨RVx.chk ⟨(0, 0), h00⟩⟩
  rw [← RotLayout.image_edgeOf hd2 dflt, Finset.filter_map, Finset.card_map]
  have hf : (univ : Finset (Fin d × Fin d)).filter
      ((fun e => ∃ w : ROut d, rotSide w = true ∧ RVx.out w ∈ e) ∘ RotLayout.edgeEmb hd1 dflt) =
      (univ : Finset (Fin d)).map ⟨fun y => ((⟨0, by omega⟩ : Fin d), y), fun y y' h => by
        simpa using congrArg Prod.snd h⟩ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp, Finset.mem_map]
    rw [show (RotLayout.edgeEmb hd1 dflt) q = RotLayout.edgeOf dflt q from rfl, RotLayout.side1_iff hd1 dflt q]
    constructor
    · intro h0
      exact ⟨q.2, Prod.ext (Fin.ext (show (0 : ℕ) = q.1 from h0.symm)) rfl⟩
    · rintro ⟨y, rfl⟩
      rfl
  rw [hf, Finset.card_map, Finset.card_univ, Fintype.card_fin]

end QEC
