import QEC.Count.Decoder
import QEC.Count.IID

/-!
# The toric code (one error sector, code capacity)

The checks are the points of the `L × L` torus; every check `(x, y)` is joined to `(x + 1, y)` and `(x, y + 1)`
(mod `L`); the edges are the qubits. There are no boundary vertices (`b1`, `b2` of `Vx` are unused). A residual
`C ∆ E` (an edge set with even degree at every check) is homologically nontrivial iff it crosses the vertical seam
(the horizontal edges between `x = L - 1` and `x = 0`) or the horizontal seam (the vertical edges between `y = L - 1`
and `y = 0`) an odd number of times; a correction fails iff its residual is nontrivial.

* `short_trivial`: an even edge set with fewer than `L` edges crosses both seams an even number of times.
* `nontrivial_cycle`: a nontrivial even edge set contains a nontrivial simple cycle, and every such cycle has at
  least `L` edges.
* `exchangeT`: the exchange lemma for a failing minimum-weight correction of least `Φ`, for alternatives with fewer
  than `L` edges in total with the window.
* `exists_phiMinFailT`, `PfailTorML_le`.
-/

namespace QEC

open Finset
open scoped symmDiff

/-- The checks of the `L × L` torus. -/
abbrev TorV (L : ℕ) := Fin L × Fin L

/-- `v` is the right or the upper neighbour of `u` on the torus. -/
def TorStep {L : ℕ} (u v : TorV L) : Prop :=
  (u.2 = v.2 ∧ ((u.1 : ℕ) + 1) % L = v.1) ∨ (u.1 = v.1 ∧ ((u.2 : ℕ) + 1) % L = v.2)

instance {L : ℕ} : DecidableRel (@TorStep L) := fun u v => by unfold TorStep; infer_instance

/-- The edges (qubits) of the toric code. -/
def torEdges (L : ℕ) : Finset (Sym2 (Vx (TorV L))) :=
  ((univ ×ˢ univ).filter (fun uv : TorV L × TorV L => TorStep uv.1 uv.2)).image
    (fun uv => s(Vx.det uv.1, Vx.det uv.2))

/-- `u v` is a horizontal edge across the vertical seam. -/
def SeamV {L : ℕ} (u v : TorV L) : Prop :=
  u.2 = v.2 ∧ (((u.1 : ℕ) = L - 1 ∧ (v.1 : ℕ) = 0) ∨ ((v.1 : ℕ) = L - 1 ∧ (u.1 : ℕ) = 0))

/-- `u v` is a vertical edge across the horizontal seam. -/
def SeamH {L : ℕ} (u v : TorV L) : Prop :=
  u.1 = v.1 ∧ (((u.2 : ℕ) = L - 1 ∧ (v.2 : ℕ) = 0) ∨ ((v.2 : ℕ) = L - 1 ∧ (u.2 : ℕ) = 0))

open scoped Classical in
/-- The number of edges of `Z` across the vertical seam. -/
noncomputable def crV {L : ℕ} (Z : Finset (Sym2 (Vx (TorV L)))) : ℕ :=
  #(Z.filter (fun e => ∃ u v : TorV L, e = s(Vx.det u, Vx.det v) ∧ SeamV u v))

open scoped Classical in
/-- The number of edges of `Z` across the horizontal seam. -/
noncomputable def crH {L : ℕ} (Z : Finset (Sym2 (Vx (TorV L)))) : ℕ :=
  #(Z.filter (fun e => ∃ u v : TorV L, e = s(Vx.det u, Vx.det v) ∧ SeamH u v))

/-- `Z` is homologically trivial (as a residual): even crossings of both seams. -/
def TrivT {L : ℕ} (Z : Finset (Sym2 (Vx (TorV L)))) : Prop := Even (crV Z) ∧ Even (crH Z)

/-- The correction `C` fails for the error `E`: the residual is nontrivial. -/
def FailsT {L : ℕ} (E C : Finset (Sym2 (Vx (TorV L)))) : Prop := ¬ TrivT (C ∆ E)

/-- The probability that some minimum-weight correction fails (toric code). -/
noncomputable def PfailTor (L : ℕ) (p : ℝ) : ℝ :=
  PrIID (torEdges L) p (fun E => ∃ C, IsMinCorr (torEdges L) (bd E) C ∧ FailsT E C)

open scoped Classical in
/-- The optimal (maximum-likelihood) failure probability: decoders from the syndrome to the class. -/
noncomputable def PfailTorML (L : ℕ) (p : ℝ) : ℝ :=
  ⨅ dec : Finset (TorV L) → Bool × Bool,
    PrIID (torEdges L) p (fun E => dec (bd E) ≠ (decide (Odd (crV E)), decide (Odd (crH E))))

/-- A failing minimum-weight correction of least `Φ` among the failing ones (toric code). -/
def IsPhiMinFailT {L : ℕ} (Φ : Sym2 (Vx (TorV L)) → ℤ) (E C : Finset (Sym2 (Vx (TorV L)))) : Prop :=
  IsMinCorr (torEdges L) (bd E) C ∧ FailsT E C ∧
    ∀ C', IsMinCorr (torEdges L) (bd E) C' → FailsT E C' → PhiS Φ C ≤ PhiS Φ C'

/-- The edge set of a closed vertex list `v₀, …, v_{n-1}` (including the edge `v_{n-1} v₀`). -/
def cycEdges {X : Type*} [DecidableEq X] : List X → Finset (Sym2 X)
  | [] => ∅
  | v :: l => pedges (v :: l ++ [v])

/-! ### Crossing parities are additive -/

theorem even_card_filter_symmDiff {α : Type*} [DecidableEq α] (A B : Finset α) (P : α → Prop)
    {_ : DecidablePred P} : Even #((A ∆ B).filter P) ↔ (Even #(A.filter P) ↔ Even #(B.filter P)) := by
  have h1 : (A ∆ B).filter P = A.filter P ∆ B.filter P := by
    ext e
    simp only [mem_filter, mem_symmDiff]
    tauto
  have h2 := card_symmDiff_add (A.filter P) (B.filter P)
  rw [h1]
  constructor
  · intro h
    constructor
    · intro hA
      obtain ⟨a, ha⟩ := h
      obtain ⟨b, hb⟩ := hA
      exact ⟨a + #((A.filter P) ∩ (B.filter P)) - b, by omega⟩
    · intro hB
      obtain ⟨a, ha⟩ := h
      obtain ⟨b, hb⟩ := hB
      exact ⟨a + #((A.filter P) ∩ (B.filter P)) - b, by omega⟩
  · intro h
    rcases Nat.even_or_odd #(A.filter P) with hA | hA
    · obtain ⟨a, ha⟩ := hA
      obtain ⟨b, hb⟩ := h.1 ⟨a, ha⟩
      exact ⟨a + b - #((A.filter P) ∩ (B.filter P)), by omega⟩
    · have hB : ¬ Even #(B.filter P) := fun hB => (Nat.not_even_iff_odd.mpr hA) (h.2 hB)
      rw [Nat.not_even_iff_odd] at hB
      obtain ⟨a, ha⟩ := hA
      obtain ⟨b, hb⟩ := hB
      exact ⟨a + b + 1 - #((A.filter P) ∩ (B.filter P)), by omega⟩

theorem even_crV_symmDiff {L : ℕ} (A B : Finset (Sym2 (Vx (TorV L)))) :
    Even (crV (A ∆ B)) ↔ (Even (crV A) ↔ Even (crV B)) := by
  unfold crV
  exact even_card_filter_symmDiff A B _

theorem even_crH_symmDiff {L : ℕ} (A B : Finset (Sym2 (Vx (TorV L)))) :
    Even (crH (A ∆ B)) ↔ (Even (crH A) ↔ Even (crH B)) := by
  unfold crH
  exact even_card_filter_symmDiff A B _

/-- Adding a trivial edge set keeps the class. -/
theorem trivT_symmDiff_iff {L : ℕ} {A B : Finset (Sym2 (Vx (TorV L)))} (hB : TrivT B) :
    TrivT (A ∆ B) ↔ TrivT A := by
  unfold TrivT
  rw [even_crV_symmDiff, even_crH_symmDiff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.2 hB.1, h2.2 hB.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun _ => hB.1, fun _ => h1⟩, ⟨fun _ => hB.2, fun _ => h2⟩⟩

/-! ### Short even edge sets: the gap argument

Cut the torus after column `k`. Every vertical edge and every horizontal edge away from the cut has both ends on
the same side, so the degree sum over the columns `≤ k` counts the edges across gap `k` and across the seam, plus
twice the edges inside. All degrees are even, so every gap is crossed with the parity of the seam; an odd parity
puts an edge in each of the `L` gaps, and an edge lies in only one gap (`L ≥ 3`). Rows are the same, with the
coordinates swapped (`p`, `q` below). -/

private theorem succ_mod_cases {L a : ℕ} (ha : a < L) :
    ((a + 1) % L = a + 1 ∧ a + 1 < L) ∨ ((a + 1) % L = 0 ∧ a + 1 = L) := by
  rcases Nat.lt_or_ge (a + 1) L with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · have h' : a + 1 = L := by omega
    refine Or.inr ⟨?_, h'⟩
    rw [h', Nat.mod_self]

private theorem torStep_ne {L : ℕ} (hL : 2 ≤ L) {u w : TorV L} (h : TorStep u w) : u ≠ w := by
  rintro rfl
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · rcases succ_mod_cases u.1.isLt with ⟨h1, -⟩ | ⟨h1, h2⟩ <;> omega
  · rcases succ_mod_cases u.2.isLt with ⟨h1, -⟩ | ⟨h1, h2⟩ <;> omega

/-- `e` is an edge `u w` with `q u = q w`, `p u = k` and `p w = k + 1` (mod `L`): it crosses the gap after the
`p`-coordinate `k`. -/
private def Gap {L : ℕ} (p q : TorV L → Fin L) (k : ℕ) (e : Sym2 (Vx (TorV L))) : Prop :=
  ∃ u w : TorV L, e = s(Vx.det u, Vx.det w) ∧ (q u : ℕ) = q w ∧ (p u : ℕ) = k ∧ (p w : ℕ) = (k + 1) % L

private instance {L : ℕ} (p q : TorV L → Fin L) (k : ℕ) : DecidablePred (Gap p q k) := fun _ => by
  unfold Gap; infer_instance

private theorem gap_mk_iff {L : ℕ} {p q : TorV L → Fin L} {k : ℕ} {u w : TorV L} :
    Gap p q k s(Vx.det u, Vx.det w) ↔
      ((q u : ℕ) = q w ∧ (p u : ℕ) = k ∧ (p w : ℕ) = (k + 1) % L) ∨
        ((q w : ℕ) = q u ∧ (p w : ℕ) = k ∧ (p u : ℕ) = (k + 1) % L) := by
  constructor
  · rintro ⟨u', w', he, h1, h2, h3⟩
    rcases Sym2.eq_iff.mp he with ⟨h4, h5⟩ | ⟨h4, h5⟩
    · simp only [Vx.det.injEq] at h4 h5
      subst h4 h5
      exact Or.inl ⟨h1, h2, h3⟩
    · simp only [Vx.det.injEq] at h4 h5
      subst h4 h5
      exact Or.inr ⟨h1, h2, h3⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨u, w, rfl, h1, h2, h3⟩
    · exact ⟨w, u, Sym2.eq_swap, h1, h2, h3⟩

/-- An edge crosses at most one gap (`L ≥ 3`). -/
private theorem gap_inj {L : ℕ} (hL : 3 ≤ L) {p q : TorV L → Fin L} {i j : ℕ} (hi : i < L) (hj : j < L)
    {e : Sym2 (Vx (TorV L))} (h1 : Gap p q i e) (h2 : Gap p q j e) : i = j := by
  obtain ⟨u, w, rfl, -, hu, hw⟩ := h1
  rcases gap_mk_iff.mp h2 with ⟨-, h3, -⟩ | ⟨-, h3, h4⟩
  · omega
  · rcases succ_mod_cases hi with ⟨h5, -⟩ | ⟨h5, h6⟩ <;>
      rcases succ_mod_cases hj with ⟨h7, -⟩ | ⟨h7, h8⟩ <;> omega

/-- The parity count for one edge `u w` and the cut after `p`-coordinate `k` (`a = p u`, `b = p w`,
`qa = q u`, `qb = q w`): ends on the near side, plus the crossings of gap `k` and of the seam, is even. -/
private theorem parity_core {L k a b qa qb : ℕ} (hL : 3 ≤ L) (hk : k + 1 < L) (ha : a < L) (hqa : qa < L)
    (hstep : (qa = qb ∧ (a + 1) % L = b) ∨ (a = b ∧ (qa + 1) % L = qb)) {A B G1 G2 : Prop}
    [Decidable A] [Decidable B] [Decidable G1] [Decidable G2] (hA : A ↔ a ≤ k) (hB : B ↔ b ≤ k)
    (hG1 : G1 ↔ (qa = qb ∧ a = k ∧ b = (k + 1) % L) ∨ (qb = qa ∧ b = k ∧ a = (k + 1) % L))
    (hG2 : G2 ↔ (qa = qb ∧ a = L - 1 ∧ b = (L - 1 + 1) % L) ∨ (qb = qa ∧ b = L - 1 ∧ a = (L - 1 + 1) % L)) :
    Even ((if A then 1 else 0) + (if B then 1 else 0) + (if G1 then 1 else 0) + (if G2 then 1 else 0)) := by
  have hk' : (k + 1) % L = k + 1 := Nat.mod_eq_of_lt hk
  have hL' : (L - 1 + 1) % L = 0 := by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  rw [hk'] at hG1
  rw [hL'] at hG2
  rw [if_congr hA rfl rfl, if_congr hB rfl rfl, Nat.even_iff]
  rcases hstep with ⟨hq, hab⟩ | ⟨hab, hq⟩
  · rcases succ_mod_cases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- a horizontal edge away from the seam: it crosses gap `k` iff `a = k`
      rw [h1] at hab
      have e1 : G1 ↔ a = k := by
        rw [hG1]
        constructor <;> intro h <;> omega
      have e2 : ¬ G2 := by rw [hG2]; omega
      rw [if_congr e1 rfl rfl, ite_eq_right e2]
      split_ifs <;> omega
    · -- a horizontal edge across the seam
      rw [h1] at hab
      have e1 : ¬ G1 := by rw [hG1]; omega
      have e2 : G2 := by rw [hG2]; omega
      rw [ite_eq_right e1, ite_eq_left e2]
      split_ifs <;> omega
  · -- a vertical edge: both ends on the same side, no crossing
    have hne : qa ≠ qb := by
      rcases succ_mod_cases hqa with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have e1 : ¬ G1 := by rw [hG1]; omega
    have e2 : ¬ G2 := by rw [hG2]; omega
    rw [ite_eq_right e1, ite_eq_right e2, hab]
    split_ifs <;> omega

private theorem sum_mem_pair {L : ℕ} (S : Finset (TorV L)) {u w : TorV L} (huw : u ≠ w) :
    ∑ v ∈ S, (if Vx.det v ∈ s(Vx.det u, Vx.det w) then 1 else 0 : ℕ) =
      (if u ∈ S then 1 else 0) + (if w ∈ S then 1 else 0) := by
  have h : ∀ v : TorV L, (if Vx.det v ∈ s(Vx.det u, Vx.det w) then 1 else 0 : ℕ) =
      (if u = v then 1 else 0) + (if w = v then 1 else 0) := by
    intro v
    simp only [Sym2.mem_iff, Vx.det.injEq]
    by_cases h1 : u = v
    · subst h1
      simp [Ne.symm huw]
    · by_cases h2 : w = v
      · subst h2
        simp [h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  rw [Finset.sum_congr rfl (fun v _ => h v), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq]

private theorem sum_vdeg_eq {L : ℕ} (Z : Finset (Sym2 (Vx (TorV L)))) (S : Finset (TorV L)) :
    ∑ v ∈ S, vdeg Z (Vx.det v) = ∑ e ∈ Z, ∑ v ∈ S, (if Vx.det v ∈ e then 1 else 0 : ℕ) := by
  simp only [vdeg, Finset.card_filter]
  exact Finset.sum_comm

/-- **The gap argument** along the `p`-coordinate. -/
private theorem even_gap_of_short {L : ℕ} (hL : 3 ≤ L) (p q : TorV L → Fin L)
    (hstep : ∀ u w : TorV L, TorStep u w →
      ((q u : ℕ) = q w ∧ ((p u : ℕ) + 1) % L = p w) ∨ ((p u : ℕ) = p w ∧ ((q u : ℕ) + 1) % L = q w))
    {Z : Finset (Sym2 (Vx (TorV L)))} (hZ : Z ⊆ torEdges L) (hbd : bd Z = ∅) (hshort : #Z < L) :
    Even #(Z.filter (Gap p q (L - 1))) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  -- every gap is crossed with the parity of the seam
  have hcut : ∀ k, k + 1 < L → Even (#(Z.filter (Gap p q k)) + #(Z.filter (Gap p q (L - 1)))) := by
    intro k hk
    set S := univ.filter (fun v : TorV L => (p v : ℕ) ≤ k) with hS
    have hev : Even (∑ v ∈ S, vdeg Z (Vx.det v)) := by
      apply even_sum_of_even
      intro v _
      have hv : v ∉ bd Z := by rw [hbd]; exact Finset.notMem_empty v
      rw [mem_bd, Nat.not_odd_iff_even] at hv
      exact hv
    rw [sum_vdeg_eq] at hev
    have hedge : ∀ e ∈ Z, Even ((∑ v ∈ S, (if Vx.det v ∈ e then 1 else 0 : ℕ)) +
        (if Gap p q k e then 1 else 0) + (if Gap p q (L - 1) e then 1 else 0)) := by
      intro e he
      obtain ⟨⟨u, w⟩, huw, rfl⟩ := Finset.mem_image.mp (hZ he)
      have hst : TorStep u w := (Finset.mem_filter.mp huw).2
      rw [sum_mem_pair S (torStep_ne (by omega) hst)]
      exact parity_core hL hk (p u).isLt (q u).isLt (hstep u w hst) (by simp [hS]) (by simp [hS])
        gap_mk_iff gap_mk_iff
    have h2 := even_sum_of_even hedge
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.card_filter, ← Finset.card_filter,
      add_assoc, Nat.even_add] at h2
    exact h2.mp hev
  -- so every gap has an edge
  have hex : ∀ k, k < L → ∃ e ∈ Z, Gap p q k e := by
    intro k hk
    have hodd' : Odd #(Z.filter (Gap p q k)) := by
      rcases Nat.lt_or_ge (k + 1) L with h | h
      · have h' := hcut k h
        rw [Nat.even_add] at h'
        rw [← Nat.not_even_iff_odd] at hodd ⊢
        exact fun h'' => hodd (h'.mp h'')
      · have hk' : k = L - 1 := by omega
        rw [hk']
        exact hodd
    obtain ⟨e, he⟩ := Finset.card_pos.mp hodd'.pos
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  -- and the gaps have distinct edges
  have hle : L ≤ #Z := by
    let f : ℕ → Sym2 (Vx (TorV L)) := fun k =>
      if hk : k < L then Classical.choose (hex k hk) else s(Vx.b1, Vx.b1)
    have hf : ∀ k (hk : k < L), f k ∈ Z ∧ Gap p q k (f k) := by
      intro k hk
      simp only [f, dite_eq_left hk]
      exact Classical.choose_spec (hex k hk)
    exact Finset.le_card_of_inj_on_range f (fun k hk => (hf k hk).1)
      (fun i hi j hj hij => gap_inj hL hi hj (hf i hi).2 (by rw [hij]; exact (hf j hj).2))
  omega

/-- **Short even edge sets are trivial.** -/
theorem short_trivial {L : ℕ} (hL : 3 ≤ L) {Z : Finset (Sym2 (Vx (TorV L)))} (hZ : Z ⊆ torEdges L)
    (hbd : bd Z = ∅) (hshort : #Z < L) : TrivT Z := by
  have hL1 : 1 ≤ L := by omega
  have hV : crV Z = #(Z.filter (Gap Prod.fst Prod.snd (L - 1))) := by
    unfold crV
    congr 1
    classical
    apply Finset.filter_congr
    intro e _
    unfold SeamV
    constructor
    · rintro ⟨u, v, rfl, h1, (⟨h2, h3⟩ | ⟨h2, h3⟩)⟩
      · exact ⟨u, v, rfl, congrArg Fin.val h1, h2, by rw [h3, Nat.sub_add_cancel hL1, Nat.mod_self]⟩
      · exact ⟨v, u, Sym2.eq_swap, congrArg Fin.val h1.symm, h2,
          by rw [h3, Nat.sub_add_cancel hL1, Nat.mod_self]⟩
    · rintro ⟨u, w, rfl, h1, h2, h3⟩
      refine ⟨u, w, rfl, Fin.ext h1, Or.inl ⟨h2, ?_⟩⟩
      rw [h3, Nat.sub_add_cancel hL1, Nat.mod_self]
  have hH : crH Z = #(Z.filter (Gap Prod.snd Prod.fst (L - 1))) := by
    unfold crH
    congr 1
    classical
    apply Finset.filter_congr
    intro e _
    unfold SeamH
    constructor
    · rintro ⟨u, v, rfl, h1, (⟨h2, h3⟩ | ⟨h2, h3⟩)⟩
      · exact ⟨u, v, rfl, congrArg Fin.val h1, h2, by rw [h3, Nat.sub_add_cancel hL1, Nat.mod_self]⟩
      · exact ⟨v, u, Sym2.eq_swap, congrArg Fin.val h1.symm, h2,
          by rw [h3, Nat.sub_add_cancel hL1, Nat.mod_self]⟩
    · rintro ⟨u, w, rfl, h1, h2, h3⟩
      refine ⟨u, w, rfl, Fin.ext h1, Or.inl ⟨h2, ?_⟩⟩
      rw [h3, Nat.sub_add_cancel hL1, Nat.mod_self]
  refine ⟨?_, ?_⟩
  · rw [hV]
    exact even_gap_of_short hL Prod.fst Prod.snd
      (fun u w h => Or.imp (fun h => ⟨congrArg Fin.val h.1, h.2⟩) (fun h => ⟨congrArg Fin.val h.1, h.2⟩) h)
      hZ hbd hshort
  · rw [hH]
    exact even_gap_of_short hL Prod.snd Prod.fst
      (fun u w h => (Or.imp (fun h => ⟨congrArg Fin.val h.1, h.2⟩)
        (fun h => ⟨congrArg Fin.val h.1, h.2⟩) h).symm) hZ hbd hshort

/-! ### Extracting a nontrivial simple cycle

Take an edge `a b` of `R`. Without it, `a` and `b` are the only odd checks, so they are joined by a simple path;
with the edge it closes a simple cycle `Γ ⊆ R` with empty boundary. If `Γ` is trivial, `R ∆ Γ` is a smaller
nontrivial even set (induction); otherwise `Γ` is the cycle, and it has at least `L` edges by `short_trivial`. -/

private theorem torEdges_notDiag {L : ℕ} (hL : 2 ≤ L) {e : Sym2 (Vx (TorV L))} (he : e ∈ torEdges L) :
    ¬ e.IsDiag := by
  obtain ⟨⟨u, w⟩, huw, rfl⟩ := Finset.mem_image.mp he
  rw [Sym2.mk_isDiag_iff, Vx.det.injEq]
  exact torStep_ne hL (Finset.mem_filter.mp huw).2

private theorem isDet_of_adj {L : ℕ} {R : Finset (Sym2 (Vx (TorV L)))} (hR : R ⊆ torEdges L)
    {x y : Vx (TorV L)} (h : (decGraph R).Adj x y) : Vx.IsDet y := by
  obtain ⟨⟨u, w⟩, -, he⟩ := Finset.mem_image.mp (hR h.2)
  rcases Sym2.eq_iff.mp he with ⟨-, h2⟩ | ⟨h1, -⟩
  · rw [← h2]; trivial
  · rw [← h1]; trivial

private theorem walk_support_isDet {L : ℕ} {R : Finset (Sym2 (Vx (TorV L)))} (hR : R ⊆ torEdges L) :
    ∀ {x y : Vx (TorV L)} (p : (decGraph R).Walk x y), Vx.IsDet x → ∀ z ∈ p.support, Vx.IsDet z
  | _, _, .nil, hx, z, hz => by
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    rw [hz]; exact hx
  | _, _, .cons h p, hx, z, hz => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact walk_support_isDet hR p (isDet_of_adj hR h) z hz

private theorem vdeg_eq_zero_of_not_isDet {L : ℕ} {R : Finset (Sym2 (Vx (TorV L)))} (hR : R ⊆ torEdges L)
    {x : Vx (TorV L)} (hx : ¬ Vx.IsDet x) : vdeg R x = 0 := by
  unfold vdeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hxe
  obtain ⟨⟨u, w⟩, -, rfl⟩ := Finset.mem_image.mp (hR he)
  rcases Sym2.mem_iff.mp hxe with rfl | rfl <;> exact hx trivial

private theorem erase_eq_symmDiff {α : Type*} [DecidableEq α] {R : Finset α} {e : α} (he : e ∈ R) :
    R.erase e = R ∆ {e} := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_symmDiff, Finset.mem_singleton]
  by_cases hx : x = e
  · subst hx; simp [he]
  · simp [hx]

private theorem length_ledges {X : Type*} : ∀ l : List X, (ledges l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by
    rw [ledges_cons_cons, List.length_cons, length_ledges (y :: l)]
    simp

private theorem ledges_append_single {X : Type*} {x y : X} :
    ∀ {l : List X}, l.getLast? = some x → ledges (l ++ [y]) = ledges l ++ [s(x, y)]
  | [], h => by simp at h
  | [z], h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    rfl
  | z :: w :: l, h => by
    have ih := ledges_append_single (y := y) (l := w :: l) (by rwa [List.getLast?_cons_cons] at h)
    simp only [List.cons_append] at ih ⊢
    rw [ledges_cons_cons, ih, ledges_cons_cons, List.cons_append]

/-- The edges of a simple path between two distinct checks have exactly those two as boundary. -/
private theorem bd_pedges_spath {V : Type*} [Fintype V] [DecidableEq V] {l : List (Vx V)} {a b : V}
    (hab : a ≠ b) (hl : l.Nodup) (hh : l.head? = some (Vx.det a)) (ht : l.getLast? = some (Vx.det b)) :
    bd (pedges l) = bd {s(Vx.det a, Vx.det b)} := by
  have hne : l ≠ [] := by rintro rfl; simp at hh
  rw [bd_singleton]
  ext v
  rw [mem_bd, vdeg_pedges hl, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Sym2.mem_iff, Vx.det.injEq]
  have h := even_countP_ledges (Vx.det v) hl hne
  rw [hh, ht] at h
  simp only [Option.some.injEq, Vx.det.injEq] at h
  rw [← Nat.not_even_iff_odd]
  by_cases h1 : a = v
  · subst h1
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hab), add_zero, Nat.even_add_one] at h
    exact ⟨fun _ => Or.inl rfl, fun _ => h⟩
  · by_cases h2 : b = v
    · subst h2
      rw [ite_eq_right h1, ite_eq_left rfl, add_zero, Nat.even_add_one] at h
      exact ⟨fun _ => Or.inr rfl, fun _ => h⟩
    · rw [ite_eq_right h1, ite_eq_right h2, add_zero, add_zero] at h
      exact ⟨fun h' => absurd h h', fun h' => h'.elim (fun h'' => absurd h''.symm h1)
        (fun h'' => absurd h''.symm h2)⟩

private theorem nontrivial_cycle_aux {L : ℕ} (hL : 3 ≤ L) : ∀ n : ℕ, ∀ R : Finset (Sym2 (Vx (TorV L))),
    #R = n → R ⊆ torEdges L → bd R = ∅ → ¬ TrivT R →
    ∃ (v0 : TorV L) (rest : List (TorV L)), (v0 :: rest).Nodup ∧ L ≤ rest.length + 1 ∧
      ((v0 :: rest).map Vx.det ++ [Vx.det v0]).IsChain (decGraph R).Adj ∧
      cycEdges ((v0 :: rest).map Vx.det) ⊆ R ∧ ¬ TrivT (cycEdges ((v0 :: rest).map Vx.det)) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih R hn hR hbd hnt
  -- an edge `a b` of `R`
  have hRne : R.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hnt ⟨by simp [crV], by simp [crH]⟩
  obtain ⟨e, he⟩ := hRne
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp (hR he)
  have hne : a ≠ b := torStep_ne (by omega) (Finset.mem_filter.mp hab).2
  -- without the edge, `a` and `b` are the odd checks, so they are joined
  set R' := R.erase s(Vx.det a, Vx.det b) with hR'
  have hR'R : R' ⊆ R := Finset.erase_subset _ _
  have hR'g : R' ⊆ torEdges L := hR'R.trans hR
  have hbd' : bd R' = univ.filter (fun v => Vx.det v ∈ s(Vx.det a, Vx.det b)) := by
    rw [hR', erase_eq_symmDiff he, bd_symmDiff, hbd, bd_singleton]
    simp
  have hreach : (decGraph R').Reachable (Vx.det a) (Vx.det b) := by
    classical
    by_contra hr
    set K := univ.filter ((decGraph R').Reachable (Vx.det a)) with hK
    have hev := even_sum_vdeg_component (fun x hx => torEdges_notDiag (by omega) (hR'g hx)) (Vx.det a)
    have haK : Vx.det a ∈ K := by simp [hK]
    rw [← Finset.add_sum_erase _ _ haK, Nat.even_add] at hev
    have hrest : Even (∑ y ∈ K.erase (Vx.det a), vdeg R' y) := by
      apply even_sum_of_even
      intro y hy
      rw [Finset.mem_erase] at hy
      cases y with
      | det v =>
        have hv : v ∉ bd R' := by
          rw [hbd']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff, Vx.det.injEq, not_or]
          refine ⟨fun h => hy.1 (by rw [h]), fun h => hr ?_⟩
          rw [← h]
          simpa [hK] using hy.2
        rwa [mem_bd, Nat.not_odd_iff_even] at hv
      | b1 => rw [vdeg_eq_zero_of_not_isDet hR'g Vx.not_isDet_b1]; exact ⟨0, rfl⟩
      | b2 => rw [vdeg_eq_zero_of_not_isDet hR'g Vx.not_isDet_b2]; exact ⟨0, rfl⟩
    have hodd : Odd (vdeg R' (Vx.det a)) := by
      have ha : a ∈ bd R' := by rw [hbd']; simp
      exact mem_bd.mp ha
    exact (Nat.not_even_iff_odd.mpr hodd) (hev.mpr hrest)
  -- a simple path from `a` to `b`; its vertices are checks
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hpdet : ∀ z ∈ p.support, Vx.IsDet z := walk_support_isDet hR'g p trivial
  let f : Vx (TorV L) → TorV L := fun z => match z with
    | .det v => v
    | _ => a
  have hf : ∀ z, Vx.IsDet z → Vx.det (f z) = z := by
    intro z hz
    cases z with
    | det v => rfl
    | b1 => exact absurd hz Vx.not_isDet_b1
    | b2 => exact absurd hz Vx.not_isDet_b2
  set rest := p.support.tail.map f with hrest
  have hmap : (a :: rest).map Vx.det = p.support := by
    rw [List.map_cons, hrest, List.map_map]
    conv_rhs => rw [← SimpleGraph.Walk.cons_tail_support p]
    congr 1
    conv_rhs => rw [← List.map_id p.support.tail]
    apply List.map_congr_left
    intro z hz
    exact hf z (hpdet z (List.mem_of_mem_tail hz))
  have hnodup : p.support.Nodup := hp.support_nodup
  have hhead : p.support.head? = some (Vx.det a) := by
    rw [List.head?_eq_some_head (SimpleGraph.Walk.support_ne_nil p), SimpleGraph.Walk.head_support]
  have hlast : p.support.getLast? = some (Vx.det b) := by
    rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil p), SimpleGraph.Walk.getLast_support]
  have hchainR' : p.support.IsChain (decGraph R').Adj := p.isChain_adj_support
  have hPR' : pedges p.support ⊆ R' := fun x hx =>
    ledges_subset_of_chain hchainR' x (List.mem_toFinset.mp hx)
  -- the cycle `Γ`: the path closed by the edge
  have hcyc : cycEdges ((a :: rest).map Vx.det) = pedges p.support ∪ {s(Vx.det a, Vx.det b)} := by
    have hsw : s(Vx.det b, Vx.det a) = s(Vx.det a, Vx.det b) := Sym2.eq_swap
    show pedges ((a :: rest).map Vx.det ++ [Vx.det a]) = _
    rw [hmap, pedges, pedges, ledges_append_single hlast, List.toFinset_append, hsw]
    simp
  set Γ := pedges p.support ∪ {s(Vx.det a, Vx.det b)} with hΓ
  have hdisj : Disjoint (pedges p.support) {s(Vx.det a, Vx.det b)} := by
    rw [Finset.disjoint_singleton_right]
    intro h
    exact (Finset.mem_erase.mp (hPR' h)).1 rfl
  have hΓR : Γ ⊆ R := Finset.union_subset (hPR'.trans hR'R) (Finset.singleton_subset_iff.mpr he)
  have hΓg : Γ ⊆ torEdges L := hΓR.trans hR
  have hΓbd : bd Γ = ∅ := by
    rw [hΓ, ← Dec_symmDiff_eq_union hdisj, bd_symmDiff, bd_pedges_spath hne hnodup hhead hlast, symmDiff_self]
    rfl
  have hchain : ((a :: rest).map Vx.det ++ [Vx.det a]).IsChain (decGraph R).Adj := by
    rw [hmap, List.isChain_append]
    refine ⟨hchainR'.imp (fun x y h => decGraph_mono hR'R h), List.isChain_singleton _, ?_⟩
    intro x hx y hy
    rw [hlast, Option.mem_some_iff] at hx
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hx hy
    exact ⟨fun h => hne (Vx.det.inj h).symm, by rw [Sym2.eq_swap]; exact he⟩
  by_cases hΓt : TrivT Γ
  · -- the rest of `R` is a smaller nontrivial even set
    have hsub : R ∆ Γ ⊆ R := by
      intro x hx
      rcases Finset.mem_symmDiff.mp hx with h | h
      · exact h.1
      · exact absurd (hΓR h.1) h.2
    have hcardlt : #(R ∆ Γ) < n := by
      have h1 := card_symmDiff_add R Γ
      rw [Finset.inter_eq_right.mpr hΓR] at h1
      have h2 : 0 < #Γ := Finset.card_pos.mpr ⟨s(Vx.det a, Vx.det b), by rw [hΓ]; simp⟩
      omega
    have hbdRG : bd (R ∆ Γ) = ∅ := by
      rw [bd_symmDiff, hbd, hΓbd, symmDiff_self]
      rfl
    have hntRG : ¬ TrivT (R ∆ Γ) := by rwa [trivT_symmDiff_iff hΓt]
    obtain ⟨v0, rest', h1, h2, h3, h4, h5⟩ := ih _ hcardlt (R ∆ Γ) rfl (hsub.trans hR) hbdRG hntRG
    exact ⟨v0, rest', h1, h2, h3.imp (fun x y h => decGraph_mono hsub h), h4.trans hsub, h5⟩
  · -- the cycle itself is nontrivial, hence long
    have hcard : L ≤ #Γ := by
      by_contra hlt
      exact hΓt (short_trivial hL hΓg hΓbd (by omega))
    have hlen : #Γ ≤ rest.length + 1 := by
      have h1 : #(cycEdges ((a :: rest).map Vx.det)) ≤
          (ledges ((a :: rest).map Vx.det ++ [Vx.det a])).length := List.toFinset_card_le _
      rw [hcyc, length_ledges, List.length_append, List.length_singleton, List.length_map,
        List.length_cons] at h1
      omega
    refine ⟨a, rest, List.Nodup.of_map Vx.det (hmap ▸ hnodup), by omega, hchain, ?_, ?_⟩
    · rw [hcyc]; exact hΓR
    · rw [hcyc]; exact hΓt

/-- **A nontrivial residual contains a nontrivial simple cycle**, of at least `L` edges. -/
theorem nontrivial_cycle {L : ℕ} (hL : 3 ≤ L) {R : Finset (Sym2 (Vx (TorV L)))} (hR : R ⊆ torEdges L)
    (hbd : bd R = ∅) (hnt : ¬ TrivT R) :
    ∃ (v0 : TorV L) (rest : List (TorV L)), (v0 :: rest).Nodup ∧ L ≤ rest.length + 1 ∧
      ((v0 :: rest).map Vx.det ++ [Vx.det v0]).IsChain (decGraph R).Adj ∧
      cycEdges ((v0 :: rest).map Vx.det) ⊆ R ∧ ¬ TrivT (cycEdges ((v0 :: rest).map Vx.det)) :=
  nontrivial_cycle_aux hL _ R rfl hR hbd hnt

theorem exists_phiMinFailT {L : ℕ} (Φ : Sym2 (Vx (TorV L)) → ℤ) {E : Finset (Sym2 (Vx (TorV L)))}
    (h : ∃ C, IsMinCorr (torEdges L) (bd E) C ∧ FailsT E C) : ∃ C, IsPhiMinFailT Φ E C := by
  classical
  set S := (torEdges L).powerset.filter (fun C => IsMinCorr (torEdges L) (bd E) C ∧ FailsT E C) with hS
  obtain ⟨C0, hC0⟩ := h
  have hne : S.Nonempty := ⟨C0, by simp only [hS, mem_filter, mem_powerset]; exact ⟨hC0.1.1, hC0⟩⟩
  obtain ⟨C, hCS, hmin⟩ := S.exists_min_image (PhiS Φ) hne
  simp only [hS, mem_filter, mem_powerset] at hCS
  refine ⟨C, hCS.2.1, hCS.2.2, fun C' hC' hf' => hmin C' ?_⟩
  simp only [hS, mem_filter, mem_powerset]
  exact ⟨hC'.1, hC', hf'⟩

/-- **The exchange lemma for the toric code** (short alternatives keep the class). -/
theorem exchangeT {L : ℕ} (hL : 3 ≤ L) {Φ : Sym2 (Vx (TorV L)) → ℤ} {E C : Finset (Sym2 (Vx (TorV L)))}
    (hC : IsPhiMinFailT Φ E C) {X Y P : List (Sym2 (Vx (TorV L)))} (hXY : (X ++ Y).Nodup)
    (hX : ∀ e ∈ X, e ∈ C) (hY : ∀ e ∈ Y, e ∉ C) (hg : ∀ e ∈ X ++ Y ++ P, e ∈ torEdges L)
    (hshort : X.length + Y.length + P.length < L) (hodd : oddD P = oddD (X ++ Y)) :
    X.length ≤ Y.length + P.length ∧
      (X.length = Y.length + P.length → P.Nodup → (X.map Φ).sum ≤ (Y.map Φ).sum + (P.map Φ).sum) := by
  classical
  obtain ⟨⟨hCE, hCA, hmin⟩, hfail, hphi⟩ := hC
  have hXn : X.Nodup := (List.nodup_append.mp hXY).1
  have hYn : Y.Nodup := (List.nodup_append.mp hXY).2.1
  have hσg : ∀ e ∈ (X ++ Y).toFinset, e ∈ torEdges L := fun e he =>
    hg e (List.mem_append_left _ (List.mem_toFinset.mp he))
  have hPg : ∀ e ∈ oddE P, e ∈ torEdges L := fun e he =>
    hg e (List.mem_append_right _ (List.mem_toFinset.mp (oddE_subset P he)))
  -- the new correction
  have hC'g : (C ∆ (X ++ Y).toFinset) ∆ oddE P ⊆ torEdges L := by
    intro e he
    rcases Finset.mem_union.mp (Finset.symmDiff_subset_union he) with h | h
    · rcases Finset.mem_union.mp (Finset.symmDiff_subset_union h) with h' | h'
      · exact hCE h'
      · exact hσg e h'
    · exact hPg e h
  have hbdσ : bd (X ++ Y).toFinset = oddD (X ++ Y) := by
    rw [← oddE_of_nodup hXY, bd_oddE]
  have hC'bd : bd ((C ∆ (X ++ Y).toFinset) ∆ oddE P) = bd E := by
    rw [bd_symmDiff, bd_symmDiff, hbdσ, bd_oddE, hodd, symmDiff_assoc, symmDiff_self, symmDiff_bot, hCA]
  -- sizes
  have hCσ : C ∩ (X ++ Y).toFinset = X.toFinset := by
    ext e
    simp only [Finset.mem_inter, List.mem_toFinset, List.mem_append]
    constructor
    · rintro ⟨hc, hx | hy⟩
      · exact hx
      · exact absurd hc (hY e hy)
    · intro hx
      exact ⟨hX e hx, Or.inl hx⟩
  have hcardC1 : #(C ∆ (X ++ Y).toFinset) + X.length = #C + Y.length := by
    have h := card_symmDiff_add C (X ++ Y).toFinset
    rw [hCσ, List.toFinset_card_of_nodup hXn, List.toFinset_card_of_nodup hXY, List.length_append] at h
    omega
  have hoddle : #(oddE P) ≤ P.length := (Finset.card_le_card (oddE_subset P)).trans (List.toFinset_card_le P)
  have hC'le : #((C ∆ (X ++ Y).toFinset) ∆ oddE P) ≤ #(C ∆ (X ++ Y).toFinset) + #(oddE P) :=
    (Finset.card_le_card Finset.symmDiff_subset_union).trans (Finset.card_union_le _ _)
  have hle := hmin _ hC'g hC'bd
  refine ⟨by omega, ?_⟩
  intro heq hPn
  -- equality: the alternative is disjoint from `C ∆ σ`, and the new correction is a failing minimizer
  have hoddP : oddE P = P.toFinset := oddE_of_nodup hPn
  have hcardP : #P.toFinset = P.length := List.toFinset_card_of_nodup hPn
  have h5 := card_symmDiff_add (C ∆ (X ++ Y).toFinset) (oddE P)
  rw [hoddP, hcardP] at h5
  rw [hoddP] at hle
  have hint0 : #((C ∆ (X ++ Y).toFinset) ∩ P.toFinset) = 0 := by omega
  have hcardC' : #((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) = #C := by omega
  have hdisjP : Disjoint (C ∆ (X ++ Y).toFinset) P.toFinset :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hint0)
  have hC'eq : (C ∆ (X ++ Y).toFinset) ∆ P.toFinset = (C ∆ (X ++ Y).toFinset) ∪ P.toFinset :=
    Dec_symmDiff_eq_union hdisjP
  rw [hoddP] at hC'g hC'bd
  have hminC' : IsMinCorr (torEdges L) (bd E) ((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) :=
    ⟨hC'g, hC'bd, fun C'' h1 h2 => by rw [hcardC']; exact hmin C'' h1 h2⟩
  -- class preservation: the toggled set is a short even edge set, hence trivial
  have hZg : (X ++ Y).toFinset ∆ P.toFinset ⊆ torEdges L := by
    intro e he
    rcases Finset.mem_union.mp (Finset.symmDiff_subset_union he) with h | h
    · exact hσg e h
    · rw [← hoddP] at h
      exact hPg e h
  have hZbd : bd ((X ++ Y).toFinset ∆ P.toFinset) = ∅ := by
    rw [bd_symmDiff, hbdσ, ← hoddP, bd_oddE, hodd, symmDiff_self]
    rfl
  have hZcard : #((X ++ Y).toFinset ∆ P.toFinset) < L := by
    have h1 : #((X ++ Y).toFinset ∆ P.toFinset) ≤ #(X ++ Y).toFinset + #P.toFinset :=
      (Finset.card_le_card Finset.symmDiff_subset_union).trans (Finset.card_union_le _ _)
    rw [List.toFinset_card_of_nodup hXY, List.length_append, hcardP] at h1
    omega
  have hZtriv := short_trivial hL hZg hZbd hZcard
  have hfailC' : FailsT E ((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) := by
    unfold FailsT at hfail ⊢
    have hset : ((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) ∆ E = (C ∆ E) ∆ ((X ++ Y).toFinset ∆ P.toFinset) := by
      ext e
      simp only [Finset.mem_symmDiff]
      by_cases h1 : e ∈ C <;> by_cases h2 : e ∈ (X ++ Y).toFinset <;> by_cases h3 : e ∈ P.toFinset <;>
        by_cases h4 : e ∈ E <;> simp only [h1, h2, h3, h4, not_true_eq_false, not_false_eq_true, and_true,
          and_false, or_false, false_or]
    rw [hset, trivT_symmDiff_iff hZtriv]
    exact hfail
  have hle2 := hphi _ hminC' hfailC'
  -- `Φ` of the new correction
  have hC1eq : C ∆ (X ++ Y).toFinset = (C \ X.toFinset) ∪ Y.toFinset := by
    ext e
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, List.mem_append]
    constructor
    · rintro (⟨hc, hn⟩ | ⟨hxy, hc⟩)
      · left; exact ⟨hc, fun hx => hn (Or.inl hx)⟩
      · rcases hxy with hx | hy
        · exact absurd (hX e hx) hc
        · right; exact hy
    · rintro (⟨hc, hx⟩ | hy)
      · left; exact ⟨hc, fun h => h.elim hx (fun hy => hY e hy hc)⟩
      · right; exact ⟨Or.inr hy, hY e hy⟩
  have hXs : X.toFinset ⊆ C := fun e he => hX e (List.mem_toFinset.mp he)
  have hphiC1 : PhiS Φ (C ∆ (X ++ Y).toFinset) = PhiS Φ C - (X.map Φ).sum + (Y.map Φ).sum := by
    unfold PhiS
    rw [hC1eq, Finset.sum_union (by
      rw [Finset.disjoint_left]
      intro e he hy
      exact hY e (List.mem_toFinset.mp hy) (Finset.mem_sdiff.mp he).1)]
    rw [Finset.sum_sdiff_eq_sub hXs, List.sum_toFinset _ hXn, List.sum_toFinset _ hYn]
  have hphiC' : PhiS Φ ((C ∆ (X ++ Y).toFinset) ∆ P.toFinset) =
      PhiS Φ (C ∆ (X ++ Y).toFinset) + (P.map Φ).sum := by
    unfold PhiS
    rw [hC'eq, Finset.sum_union hdisjP, List.sum_toFinset _ hPn]
  rw [hphiC', hphiC1] at hle2
  linarith

/-- ML decoding is at least as good as any minimum-weight decoder (toric code). -/
theorem PfailTorML_le (L : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PfailTorML L p ≤ PfailTor L p := by
  classical
  -- a minimum-weight decoder with a syndrome-only tie rule (a chosen minimizer), reporting its class
  let dec : Finset (TorV L) → Bool × Bool := fun s =>
    if h : ∃ C, IsMinCorr (torEdges L) s C then
      (decide (Odd (crV (Classical.choose h))), decide (Odd (crH (Classical.choose h)))) else (false, false)
  have hle : PfailTorML L p ≤
      PrIID (torEdges L) p (fun E => dec (bd E) ≠ (decide (Odd (crV E)), decide (Odd (crH E)))) := by
    unfold PfailTorML
    exact ciInf_le (Set.finite_range _).bddBelow dec
  refine le_trans hle (PrIID_mono (torEdges L) hp0 hp1 ?_)
  intro E hE hne
  -- the syndrome of `E` has a minimizer: `E` is a correction, and there are finitely many
  have hex : ∃ C, IsMinCorr (torEdges L) (bd E) C := by
    have hne' : ((torEdges L).powerset.filter (fun C => bd C = bd E)).Nonempty :=
      ⟨E, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hE, rfl⟩⟩
    obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image _ (fun C => #C) hne'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hC
    exact ⟨C, hC.1, hC.2, fun C' hC' hbd =>
      hmin C' (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC', hbd⟩)⟩
  refine ⟨Classical.choose hex, Classical.choose_spec hex, ?_⟩
  have hdec : dec (bd E) = (decide (Odd (crV (Classical.choose hex))), decide (Odd (crH (Classical.choose hex)))) := by
    simp [dec, hex]
  rw [hdec] at hne
  intro htriv
  apply hne
  obtain ⟨h1, h2⟩ := htriv
  rw [even_crV_symmDiff] at h1
  rw [even_crH_symmDiff] at h2
  have e1 : Odd (crV (Classical.choose hex)) ↔ Odd (crV E) := by
    rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd, h1]
  have e2 : Odd (crH (Classical.choose hex)) ↔ Odd (crH E) := by
    rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd, h2]
  rw [Prod.mk.injEq]
  exact ⟨decide_eq_decide.mpr e1, decide_eq_decide.mpr e2⟩

end QEC
