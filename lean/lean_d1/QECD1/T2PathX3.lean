import QECD1.T2Path3

/-!
# The `C_top` paths of a T2 path, and (X) on them (3D)

The 3D analogue of the second part of the 2D `TwoD/T2Path`.

* `stepE3`, `edgeOf3`: the `C_top` edge carried by a step of `Γ` (a bulk edge between two checks, a half-edge between
  a check and a boundary; none at a family node). `Pl3 l`: the `C_top` paths of a `Γ`-chain `l`, the edges of all its
  steps; they lie in `C_top` (`Pl3_subset`).
* `psyn3_Pl3`: the odd checks of `Pl3 l` are the checks next to the family nodes of `l` (`stT3`), plus the end nodes
  if they are checks.
* `pairCost3`: the minimum weight of an edge set with given odd checks.
* `path_X3`, `path_X_pairs3`, `T2ev_X3` ((X), the exchange): `C_top` is a minimum-weight correction of `Ω`, so
  its paths weigh at most any edge set with the same odd checks; on a T2 path, at most the sum over its family nodes
  of the pair costs of their neighbouring checks.
-/

open Finset

namespace QECD1

open Classical

variable {T w h : ℕ}

/-- The node at position `k` (a default beyond the end). -/
def nd3 (l : List (GNode3 T w h)) (k : ℕ) : GNode3 T w h := (l[k]?).getD (.inr (.inl false))

/-- The syndrome of a single check (zero at the other nodes). -/
noncomputable def sOf3 : GNode3 T w h → PVert3 T w h → ZMod 2
  | .inl u => Pi.single u 1
  | _ => 0

/-- The node is a family node. -/
def isFam3 (z : GNode3 T w h) : Prop := ∃ F, z = .inr (.inr F)

theorem sOf3_of_not_check {z : GNode3 T w h} (hz : ∀ u, z ≠ .inl u) : sOf3 z = 0 := by
  rcases z with u | b | F
  · exact absurd rfl (hz u)
  · rfl
  · rfl

theorem sOf3_fam {z : GNode3 T w h} (hz : isFam3 z) : sOf3 z = 0 := by
  obtain ⟨F, rfl⟩ := hz
  rfl

theorem nd3_of_getElem? {l : List (GNode3 T w h)} {k : ℕ} {z : GNode3 T w h} (hk : l[k]? = some z) :
    nd3 l k = z := by
  simp [nd3, hk]

theorem fun_add_self3 (x : PVert3 T w h → ZMod 2) : x + x = 0 := by
  funext v
  exact CharTwo.add_self_eq_zero _

theorem psyn3_single_apply (e : PEdge3 T w h) (v : PVert3 T w h) :
    psyn3 (Pi.single e 1) v = if v ∈ e.ends then 1 else 0 := by
  rw [psyn3_single]

/-- The odd checks contributed by the node at position `k` of `l` (for a family node): its neighbouring checks. -/
noncomputable def stT3 (l : List (GNode3 T w h)) (k : ℕ) : PVert3 T w h → ZMod 2 :=
  (if 0 < k then sOf3 (nd3 l (k - 1)) else 0) + (if k + 1 < l.length then sOf3 (nd3 l (k + 1)) else 0)

theorem telescope3 (f : ℕ → PVert3 T w h → ZMod 2) (m : ℕ) :
    ∑ j ∈ Finset.range m, (f j + f (j + 1)) = f 0 + f m := by
  induction m with
  | zero =>
    funext v
    simp only [Finset.range_zero, Finset.sum_empty, Pi.zero_apply, Pi.add_apply]
    exact (CharTwo.add_self_eq_zero _).symm
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    funext v
    simp only [Pi.add_apply]
    linear_combination CharTwo.add_self_eq_zero (f m v)

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- The `C_top` edge carried by a step of `Γ`. -/
def stepE3 (E : PEdge3 T w h → ZMod 2) : GNode3 T w h → GNode3 T w h → PEdge3 T w h → Prop
  | .inl u, .inl v, e => e.ends = {u, v} ∧ u ≠ v ∧ S.ctop3 Z E e ≠ 0
  | .inl u, .inr (.inl false), e => ∃ t x, u = (t, x, 0) ∧ e = .bot t x ∧ S.ctop3 Z E e ≠ 0
  | .inr (.inl false), .inl u, e => ∃ t x, u = (t, x, 0) ∧ e = .bot t x ∧ S.ctop3 Z E e ≠ 0
  | .inl u, .inr (.inl true), e => ∃ t x, u = (t, x, Fin.last h) ∧ e = .top t x ∧ S.ctop3 Z E e ≠ 0
  | .inr (.inl true), .inl u, e => ∃ t x, u = (t, x, Fin.last h) ∧ e = .top t x ∧ S.ctop3 Z E e ≠ 0
  | _, _, _ => False

/-- The edge of a step (chosen), as an edge set. -/
noncomputable def edgeOf3 (E : PEdge3 T w h → ZMod 2) (x y : GNode3 T w h) : PEdge3 T w h → ZMod 2 :=
  if hxy : ∃ e, S.stepE3 Z E x y e then Pi.single (Classical.choose hxy) 1 else 0

/-- **The `C_top` paths of a `Γ`-chain**: the edges of all its steps. -/
noncomputable def Pl3 (E : PEdge3 T w h → ZMod 2) (l : List (GNode3 T w h)) : PEdge3 T w h → ZMod 2 :=
  ∑ k ∈ Finset.range (l.length - 1), S.edgeOf3 Z E (nd3 l k) (nd3 l (k + 1))

theorem stepE3_ctop {E : PEdge3 T w h → ZMod 2} {x y : GNode3 T w h} {e : PEdge3 T w h}
    (hxy : S.stepE3 Z E x y e) : S.ctop3 Z E e ≠ 0 := by
  rcases x with u | (_ | _) | F <;> rcases y with v | (_ | _) | F' <;> simp only [stepE3] at hxy
  · exact hxy.2.2
  · obtain ⟨_, _, _, _, hc⟩ := hxy; exact hc
  · obtain ⟨_, _, _, _, hc⟩ := hxy; exact hc
  · obtain ⟨_, _, _, _, hc⟩ := hxy; exact hc
  · obtain ⟨_, _, _, _, hc⟩ := hxy; exact hc

/-- **The `C_top` paths lie in `C_top`.** -/
theorem Pl3_subset {E : PEdge3 T w h → ZMod 2} (l : List (GNode3 T w h)) (e : PEdge3 T w h)
    (he : S.Pl3 Z E l e ≠ 0) : S.ctop3 Z E e ≠ 0 := by
  unfold Pl3 at he
  rw [Finset.sum_apply] at he
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  unfold edgeOf3 at hk
  split_ifs at hk with hex
  · have he' : e = Classical.choose hex := by
      by_contra hne
      exact hk (by simp [hne])
    rw [he']
    exact S.stepE3_ctop Z (Classical.choose_spec hex)
  · exact absurd rfl hk

/-- The syndrome of the edge of a step of `Γ`. -/
theorem psyn3_edgeOf3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {x y : GNode3 T w h} (hxy : S.gadj3 Z ny E x y) :
    psyn3 (S.edgeOf3 Z E x y) = if isFam3 x ∨ isFam3 y then 0 else sOf3 x + sOf3 y := by
  have hsingle : ∀ (hex : ∃ e, S.stepE3 Z E x y e),
      psyn3 (S.edgeOf3 Z E x y) = psyn3 (Pi.single (Classical.choose hex) 1) := by
    intro hex
    unfold edgeOf3
    rw [dite_eq_left hex]
  have hzero : (¬ ∃ e, S.stepE3 Z E x y e) → psyn3 (S.edgeOf3 Z E x y) = 0 := by
    intro hne
    unfold edgeOf3
    rw [dite_eq_right hne]
    exact psyn3_zero
  rcases x with u | (_ | _) | F <;> rcases y with v | (_ | _) | F'
  -- two checks
  · have hex : ∃ e, S.stepE3 Z E (.inl u) (.inl v) e := by
      rcases hxy with ⟨e, he, hne, hc⟩ | ⟨e, he, hne, hc⟩
      · exact ⟨e, he, hne, hc⟩
      · exact ⟨e, by rw [he, Finset.pair_comm], hne.symm, hc⟩
    rw [hsingle hex]
    obtain ⟨hends, hne, _⟩ := Classical.choose_spec hex
    have hnf : ¬ (isFam3 (.inl u : GNode3 T w h) ∨ isFam3 (.inl v : GNode3 T w h)) := by
      rintro (⟨F, hF⟩ | ⟨F, hF⟩) <;> cases hF
    rw [ite_eq_right hnf]
    funext z
    rw [psyn3_single_apply, hends]
    simp only [sOf3, Pi.add_apply, Pi.single_apply, Finset.mem_insert, Finset.mem_singleton]
    by_cases hzu : z = u <;> by_cases hzv : z = v
    · exact absurd (hzu.symm.trans hzv) hne
    · subst hzu
      simp [hne]
    · subst hzv
      simp [hne.symm]
    · simp [hzu, hzv]
  -- check and b₁
  · have hex : ∃ e, S.stepE3 Z E (.inl u) (.inr (.inl false)) e := by
      rcases hxy with ⟨t, x, hx, hc⟩ | hc
      · exact ⟨_, t, x, hx, rfl, hc⟩
      · simp [gadj0] at hc
    rw [hsingle hex]
    obtain ⟨t, x, hx, hex', _⟩ := Classical.choose_spec hex
    have hnf : ¬ (isFam3 (.inl u : GNode3 T w h) ∨ isFam3 (.inr (.inl false) : GNode3 T w h)) := by
      rintro (⟨F, hF⟩ | ⟨F, hF⟩) <;> cases hF
    rw [ite_eq_right hnf, hex']
    funext z
    rw [psyn3_single_apply, hx]
    simp [sOf3, PEdge3.ends, Pi.single_apply]
  -- check and b₂
  · have hex : ∃ e, S.stepE3 Z E (.inl u) (.inr (.inl true)) e := by
      rcases hxy with ⟨t, x, hx, hc⟩ | hc
      · exact ⟨_, t, x, hx, rfl, hc⟩
      · simp [gadj0] at hc
    rw [hsingle hex]
    obtain ⟨t, x, hx, hex', _⟩ := Classical.choose_spec hex
    have hnf : ¬ (isFam3 (.inl u : GNode3 T w h) ∨ isFam3 (.inr (.inl true) : GNode3 T w h)) := by
      rintro (⟨F, hF⟩ | ⟨F, hF⟩) <;> cases hF
    rw [ite_eq_right hnf, hex']
    funext z
    rw [psyn3_single_apply, hx]
    simp [sOf3, PEdge3.ends, Pi.single_apply]
  -- check and family
  · rw [ite_eq_left (Or.inr ⟨F', rfl⟩), hzero (by rintro ⟨e, he⟩; simp [stepE3] at he)]
  -- b₁ and check
  · have hex : ∃ e, S.stepE3 Z E (.inr (.inl false)) (.inl v) e := by
      rcases hxy with hc | ⟨t, x, hx, hc⟩
      · simp [gadj0] at hc
      · exact ⟨_, t, x, hx, rfl, hc⟩
    rw [hsingle hex]
    obtain ⟨t, x, hx, hex', _⟩ := Classical.choose_spec hex
    have hnf : ¬ (isFam3 (.inr (.inl false) : GNode3 T w h) ∨ isFam3 (.inl v : GNode3 T w h)) := by
      rintro (⟨F, hF⟩ | ⟨F, hF⟩) <;> cases hF
    rw [ite_eq_right hnf, hex']
    funext z
    rw [psyn3_single_apply, hx]
    simp [sOf3, PEdge3.ends, Pi.single_apply]
  -- boundary to boundary: no step
  · rcases hxy with hc | hc <;> simp [gadj0] at hc
  · rcases hxy with hc | hc <;> simp [gadj0] at hc
  · rw [ite_eq_left (Or.inr ⟨F', rfl⟩), hzero (by rintro ⟨e, he⟩; simp [stepE3] at he)]
  -- b₂ and check
  · have hex : ∃ e, S.stepE3 Z E (.inr (.inl true)) (.inl v) e := by
      rcases hxy with hc | ⟨t, x, hx, hc⟩
      · simp [gadj0] at hc
      · exact ⟨_, t, x, hx, rfl, hc⟩
    rw [hsingle hex]
    obtain ⟨t, x, hx, hex', _⟩ := Classical.choose_spec hex
    have hnf : ¬ (isFam3 (.inr (.inl true) : GNode3 T w h) ∨ isFam3 (.inl v : GNode3 T w h)) := by
      rintro (⟨F, hF⟩ | ⟨F, hF⟩) <;> cases hF
    rw [ite_eq_right hnf, hex']
    funext z
    rw [psyn3_single_apply, hx]
    simp [sOf3, PEdge3.ends, Pi.single_apply]
  · rcases hxy with hc | hc <;> simp [gadj0] at hc
  · rcases hxy with hc | hc <;> simp [gadj0] at hc
  · rw [ite_eq_left (Or.inr ⟨F', rfl⟩), hzero (by rintro ⟨e, he⟩; simp [stepE3] at he)]
  -- a family first
  · rw [ite_eq_left (Or.inl ⟨F, rfl⟩), hzero (by rintro ⟨e, he⟩; simp [stepE3] at he)]
  · rw [ite_eq_left (Or.inl ⟨F, rfl⟩), hzero (by rintro ⟨e, he⟩; simp [stepE3] at he)]
  · rw [ite_eq_left (Or.inl ⟨F, rfl⟩), hzero (by rintro ⟨e, he⟩; simp [stepE3] at he)]
  · rw [ite_eq_left (Or.inl ⟨F, rfl⟩), hzero (by rintro ⟨e, he⟩; simp [stepE3] at he)]

/-- **The odd checks of the `C_top` paths of a `Γ`-chain**: the checks next to its family nodes, plus its end nodes if
they are checks. -/
theorem psyn3_Pl3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {l : List (GNode3 T w h)}
    (hch : List.IsChain (S.gadj3 Z ny E) l) (hl : l ≠ []) :
    psyn3 (S.Pl3 Z E l) =
      (∑ k ∈ Finset.range l.length, if isFam3 (nd3 l k) then stT3 l k else 0) + sOf3 (nd3 l 0) +
        sOf3 (nd3 l (l.length - 1)) := by
  have hn : 1 ≤ l.length := List.length_pos_of_ne_nil hl
  obtain ⟨m, hm⟩ : ∃ m, l.length = m + 1 := ⟨l.length - 1, by omega⟩
  have hstep : ∀ j ∈ Finset.range m, psyn3 (S.edgeOf3 Z E (nd3 l j) (nd3 l (j + 1))) =
      if isFam3 (nd3 l j) ∨ isFam3 (nd3 l (j + 1)) then 0 else sOf3 (nd3 l j) + sOf3 (nd3 l (j + 1)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj1 : j < l.length := by omega
    have hj2 : j + 1 < l.length := by omega
    have e1 : l[j]? = some (nd3 l j) := by simp [nd3, List.getElem?_eq_getElem hj1]
    have e2 : l[j + 1]? = some (nd3 l (j + 1)) := by simp [nd3, List.getElem?_eq_getElem hj2]
    exact S.psyn3_edgeOf3 Z (chain_step hch e1 e2)
  have hst : (∑ k ∈ Finset.range l.length, if isFam3 (nd3 l k) then stT3 l k else 0) =
      ∑ j ∈ Finset.range m, ((if isFam3 (nd3 l (j + 1)) then sOf3 (nd3 l j) else 0) +
        (if isFam3 (nd3 l j) then sOf3 (nd3 l (j + 1)) else 0)) := by
    have hsplit : ∀ k, (if isFam3 (nd3 l k) then stT3 l k else 0) =
        (if isFam3 (nd3 l k) then (if 0 < k then sOf3 (nd3 l (k - 1)) else 0) else 0) +
          (if isFam3 (nd3 l k) then (if k + 1 < l.length then sOf3 (nd3 l (k + 1)) else 0) else 0) := by
      intro k
      unfold stT3
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_add_distrib, hm,
      Finset.sum_range_succ', Finset.sum_range_succ]
    have h0 : (if isFam3 (nd3 l 0) then (if 0 < 0 then sOf3 (nd3 l (0 - 1)) else 0) else 0) = 0 := by simp
    have hlast : (if isFam3 (nd3 l m) then (if m + 1 < m + 1 then sOf3 (nd3 l (m + 1)) else 0) else 0) = 0 := by
      simp
    rw [h0, hlast, add_zero, add_zero]
    have h1 : ∀ j ∈ Finset.range m, (if isFam3 (nd3 l (j + 1)) then
        (if 0 < j + 1 then sOf3 (nd3 l (j + 1 - 1)) else 0) else 0) =
          if isFam3 (nd3 l (j + 1)) then sOf3 (nd3 l j) else 0 := fun j _ => by simp
    have h2 : ∀ j ∈ Finset.range m, (if isFam3 (nd3 l j) then
        (if j + 1 < m + 1 then sOf3 (nd3 l (j + 1)) else 0) else 0) =
          if isFam3 (nd3 l j) then sOf3 (nd3 l (j + 1)) else 0 := fun j hj => by
      rw [Finset.mem_range] at hj
      have : j + 1 < m + 1 := by omega
      simp [this]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  rw [hst]
  have hpt : ∀ j, (if isFam3 (nd3 l j) ∨ isFam3 (nd3 l (j + 1)) then 0 else sOf3 (nd3 l j) + sOf3 (nd3 l (j + 1))) +
      ((if isFam3 (nd3 l (j + 1)) then sOf3 (nd3 l j) else 0) +
        (if isFam3 (nd3 l j) then sOf3 (nd3 l (j + 1)) else 0)) =
      sOf3 (nd3 l j) + sOf3 (nd3 l (j + 1)) := by
    intro j
    by_cases h1 : isFam3 (nd3 l j) <;> by_cases h2 : isFam3 (nd3 l (j + 1))
    · simp [h1, h2, sOf3_fam h1, sOf3_fam h2]
    · simp [h1, h2, sOf3_fam h1]
    · simp [h1, h2, sOf3_fam h2]
    · simp [h1, h2]
  have htot : psyn3 (S.Pl3 Z E l) + ∑ j ∈ Finset.range m,
      ((if isFam3 (nd3 l (j + 1)) then sOf3 (nd3 l j) else 0) +
        (if isFam3 (nd3 l j) then sOf3 (nd3 l (j + 1)) else 0)) =
      sOf3 (nd3 l 0) + sOf3 (nd3 l m) := by
    unfold Pl3
    rw [psyn3_sum, hm, Nat.add_sub_cancel, Finset.sum_congr rfl hstep, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun j _ => hpt j, telescope3 (fun j => sOf3 (nd3 l j)) m]
  rw [hm, Nat.add_sub_cancel]
  set B := ∑ j ∈ Finset.range m,
    ((if isFam3 (nd3 l (j + 1)) then sOf3 (nd3 l j) else 0) + (if isFam3 (nd3 l j) then sOf3 (nd3 l (j + 1)) else 0))
  calc psyn3 (S.Pl3 Z E l) = psyn3 (S.Pl3 Z E l) + (B + B) := by rw [fun_add_self3, add_zero]
    _ = (psyn3 (S.Pl3 Z E l) + B) + B := by rw [add_assoc]
    _ = (sOf3 (nd3 l 0) + sOf3 (nd3 l m)) + B := by rw [htot]
    _ = B + sOf3 (nd3 l 0) + sOf3 (nd3 l m) := by abel

end Stage13

/-! ### Pair costs and (X) -/

/-- The minimum weight of an edge set with odd checks `S` (the pair cost of `S`). -/
noncomputable def pairCost3 (wt : PEdge3 T w h → ℝ) (Sy : PVert3 T w h → ZMod 2) : ℝ :=
  if hne : (Finset.univ.filter (fun X : PEdge3 T w h → ZMod 2 => psyn3 X = Sy)).Nonempty then
    (Finset.univ.filter (fun X : PEdge3 T w h → ZMod 2 => psyn3 X = Sy)).inf' hne (wsum3 wt) else 0

theorem psyn3_surj (Sy : PVert3 T w h → ZMod 2) : ∃ X : PEdge3 T w h → ZMod 2, psyn3 X = Sy := by
  obtain ⟨X, _, hX⟩ := realizable_of_rough (T := T) (w := w) (h := h) conn3_univ (Set.mem_univ (0, 0, 0))
    (Or.inl rfl) (S := Sy) (fun v _ => Set.mem_univ v)
  exact ⟨X, hX⟩

theorem pairCost3_le {wt : PEdge3 T w h → ℝ} {Sy : PVert3 T w h → ZMod 2} {X : PEdge3 T w h → ZMod 2}
    (hX : psyn3 X = Sy) : pairCost3 wt Sy ≤ wsum3 wt X := by
  have hne : (Finset.univ.filter (fun X : PEdge3 T w h → ZMod 2 => psyn3 X = Sy)).Nonempty := ⟨X, by simp [hX]⟩
  unfold pairCost3
  rw [dite_eq_left hne]
  exact Finset.inf'_le _ (by simp [hX])

theorem exists_pairCost3 (wt : PEdge3 T w h → ℝ) (Sy : PVert3 T w h → ZMod 2) :
    ∃ X : PEdge3 T w h → ZMod 2, psyn3 X = Sy ∧ wsum3 wt X = pairCost3 wt Sy := by
  obtain ⟨X0, hX0⟩ := psyn3_surj Sy
  have hne : (Finset.univ.filter (fun X : PEdge3 T w h → ZMod 2 => psyn3 X = Sy)).Nonempty := ⟨X0, by simp [hX0]⟩
  obtain ⟨X, hXmem, hXeq⟩ := Finset.exists_mem_eq_inf' hne (wsum3 wt)
  refine ⟨X, (Finset.mem_filter.1 hXmem).2, ?_⟩
  unfold pairCost3
  rw [dite_eq_left hne, hXeq]

theorem wsum3_nonneg {wt : PEdge3 T w h → ℝ} (hwt : ∀ e, 0 ≤ wt e) (X : PEdge3 T w h → ZMod 2) : 0 ≤ wsum3 wt X :=
  Finset.sum_nonneg fun e _ => by
    split_ifs
    · exact hwt e
    · exact le_rfl

theorem pairCost3_nonneg {wt : PEdge3 T w h → ℝ} (hwt : ∀ e, 0 ≤ wt e) (Sy : PVert3 T w h → ZMod 2) :
    0 ≤ pairCost3 wt Sy := by
  obtain ⟨X, -, hX⟩ := exists_pairCost3 wt Sy
  rw [← hX]
  exact wsum3_nonneg hwt X

theorem pairCost3_zero {wt : PEdge3 T w h → ℝ} (hwt : ∀ e, 0 ≤ wt e) :
    pairCost3 wt (0 : PVert3 T w h → ZMod 2) = 0 := by
  refine le_antisymm ?_ (pairCost3_nonneg hwt 0)
  have hle := pairCost3_le (wt := wt) (X := (0 : PEdge3 T w h → ZMod 2)) psyn3_zero
  simpa [wsum3] using hle

theorem pairCost3_add_le {wt : PEdge3 T w h → ℝ} (hwt : ∀ e, 0 ≤ wt e) (S1 S2 : PVert3 T w h → ZMod 2) :
    pairCost3 wt (S1 + S2) ≤ pairCost3 wt S1 + pairCost3 wt S2 := by
  obtain ⟨X, hX, hXc⟩ := exists_pairCost3 wt S1
  obtain ⟨X', hX', hXc'⟩ := exists_pairCost3 wt S2
  calc pairCost3 wt (S1 + S2) ≤ wsum3 wt (X + X') := pairCost3_le (by rw [psyn3_add, hX, hX'])
    _ ≤ wsum3 wt X + wsum3 wt X' := wsum3_add_le hwt X X'
    _ = pairCost3 wt S1 + pairCost3 wt S2 := by rw [hXc, hXc']

theorem pairCost3_sum_le {wt : PEdge3 T w h → ℝ} (hwt : ∀ e, 0 ≤ wt e) {ι : Type} (s : Finset ι)
    (Sy : ι → PVert3 T w h → ZMod 2) : pairCost3 wt (∑ i ∈ s, Sy i) ≤ ∑ i ∈ s, pairCost3 wt (Sy i) := by
  induction s using Finset.induction_on with
  | empty => simp [pairCost3_zero hwt]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (pairCost3_add_le hwt _ _).trans (add_le_add le_rfl ih)

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- `C_top` is a minimum-weight edge set for its syndrome. -/
theorem ctop3_min (E : PEdge3 T w h → ZMod 2) :
    ∀ Y, psyn3 Y = psyn3 (S.ctop3 Z E) → wsum3 Z.wt (S.ctop3 Z E) ≤ wsum3 Z.wt Y := by
  intro Y hY
  rw [S.psyn3_ctop3] at hY
  exact Z.minimal _ _ Y (fun _ _ _ _ => Set.mem_univ _) hY

/-- **(X), general form, on a `Γ`-chain**: the `C_top` paths weigh at most any edge set with the same odd checks. -/
theorem path_X3 (hwt : ∀ e, 0 ≤ Z.wt e) {E : PEdge3 T w h → ZMod 2} (l : List (GNode3 T w h))
    {P' : PEdge3 T w h → ZMod 2} (hP' : psyn3 P' = psyn3 (S.Pl3 Z E l)) :
    wsum3 Z.wt (S.Pl3 Z E l) ≤ wsum3 Z.wt P' :=
  exchange3 Z.wt hwt (S.ctop3_min Z E) (fun e he => S.Pl3_subset Z l e he) hP'

/-- **(X) with pair costs, on a `Γ`-chain whose end nodes are not checks**: the `C_top` paths weigh at most the sum,
over the family nodes of the chain, of the pair cost of their neighbouring checks. -/
theorem path_X_pairs3 (hwt : ∀ e, 0 ≤ Z.wt e) {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {l : List (GNode3 T w h)}
    (hch : List.IsChain (S.gadj3 Z ny E) l) (hl : l ≠ []) (h0 : ∀ u, nd3 l 0 ≠ .inl u)
    (hlast : ∀ u, nd3 l (l.length - 1) ≠ .inl u) :
    wsum3 Z.wt (S.Pl3 Z E l) ≤
      ∑ k ∈ Finset.range l.length, if isFam3 (nd3 l k) then pairCost3 Z.wt (stT3 l k) else 0 := by
  obtain ⟨X, hX, hXc⟩ := exists_pairCost3 Z.wt (psyn3 (S.Pl3 Z E l))
  have hpsyn := S.psyn3_Pl3 Z hch hl
  rw [sOf3_of_not_check h0, sOf3_of_not_check hlast, add_zero, add_zero] at hpsyn
  calc wsum3 Z.wt (S.Pl3 Z E l) ≤ wsum3 Z.wt X := S.path_X3 Z hwt l hX
    _ = pairCost3 Z.wt (psyn3 (S.Pl3 Z E l)) := hXc
    _ = pairCost3 Z.wt (∑ k ∈ Finset.range l.length, if isFam3 (nd3 l k) then stT3 l k else 0) := by rw [hpsyn]
    _ ≤ ∑ k ∈ Finset.range l.length, pairCost3 Z.wt (if isFam3 (nd3 l k) then stT3 l k else 0) :=
        pairCost3_sum_le hwt _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs
        · rfl
        · exact pairCost3_zero hwt

/-- **(X) on the T2 event**: for the path of `T2ev3` (its ends are boundaries or family nodes). -/
theorem T2ev_X3 (hwt : ∀ e, 0 ≤ Z.wt e) {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {l : List (GNode3 T w h)}
    {x y : GNode3 T w h} (hhd : l.head? = some x) (hlst : l.getLast? = some y)
    (hch : List.IsChain (S.gadj3 Z ny E) l)
    (hx : x = .inr (.inl false) ∨ S.botFam3 ny E x) (hy : y = .inr (.inl true) ∨ S.topFam3 ny E y) :
    wsum3 Z.wt (S.Pl3 Z E l) ≤
      ∑ k ∈ Finset.range l.length, if isFam3 (nd3 l k) then pairCost3 Z.wt (stT3 l k) else 0 := by
  have hl : l ≠ [] := by
    rintro rfl
    simp at hhd
  have hnd0 : nd3 l 0 = x := nd3_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd)
  have hndl : nd3 l (l.length - 1) = y := nd3_of_getElem? (by rw [← List.getLast?_eq_getElem?]; exact hlst)
  refine S.path_X_pairs3 Z hwt hch hl ?_ ?_
  · intro u hu
    rw [hnd0] at hu
    subst hu
    rcases hx with hc | hc
    · cases hc
    · exact hc
  · intro u hu
    rw [hndl] at hu
    subst hu
    rcases hy with hc | hc
    · cases hc
    · exact hc

end Stage13

end QECD1
