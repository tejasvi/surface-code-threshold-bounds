import QECML.TwoD.LemmaX

/-!
# The T2 event

`T2ev`: a simple path of the graph `Γ` of Lemma C that starts at `b₁` or at a bottom-strip family node, ends at `b₂`
or at a top-strip family node, and whose other family nodes are intermediate (in `families`, no block in either
strip). Its family nodes are distinct; between consecutive family nodes it runs through checks joined by bulk edges of
`C_top` (the `C_top` paths of the paper's proof), and at a boundary end through a half-edge of `C_top`. This is the
sub-path used for the ends in the paper's proof: from the last bottom-strip family `F₀` (or `b₁` if there is none)
to the first top-strip family after it (or `b₂`).

* `T2ev_of_fails`: if S3' fails, `T2ev` holds (from `lemmaC_path`: cut the path at the last bottom-strip family node
  and at the first top-strip family node after it).
-/

open Finset Classical

namespace QECML

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- A family node whose family has a block in the bottom strip. -/
def botFam (a0 a1 : ℕ) (E : G.Ed → ZMod 2) : G.GNode → Prop
  | .inr (.inr Fm) => Fm ∈ S.families a0 a1 E ∧ ∃ c ∈ Fm, c.2.val ≤ hs a1
  | _ => False

/-- A family node whose family has a block in the top strip. -/
def topFam (a0 a1 : ℕ) (E : G.Ed → ZMod 2) : G.GNode → Prop
  | .inr (.inr Fm) => Fm ∈ S.families a0 a1 E ∧ ∃ c ∈ Fm, G.ny ≤ c.2.val + 1 + hs a1
  | _ => False

/-- An intermediate node: a check, a boundary, or a family with no block in either strip. -/
def interFam (a0 a1 : ℕ) (E : G.Ed → ZMod 2) : G.GNode → Prop
  | .inr (.inr Fm) => Fm ∈ S.families a0 a1 E ∧ ∀ c ∈ Fm, hs a1 < c.2.val ∧ c.2.val + 1 + hs a1 < G.ny
  | _ => True

/-- **The note's T2 event** (path form): a simple path of `Γ` from `x` (`b₁` or a bottom-strip family node) to `y`
(`b₂` or a top-strip family node), passing through the boundaries only at its ends, whose other family nodes are
intermediate. -/
def T2ev (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) : Prop :=
  ∃ (l : List G.GNode) (x y : G.GNode), l.head? = some x ∧ l.getLast? = some y ∧ l.Nodup ∧
    List.IsChain (S.gadj a0 a1 Z E) l ∧
    (x = .inr (.inl false) ∨ S.botFam a0 a1 E x) ∧ (y = .inr (.inl true) ∨ S.topFam a0 a1 E y) ∧
    (∀ b : Bool, (.inr (.inl b) : G.GNode) ∈ l → (.inr (.inl b) : G.GNode) = x ∨ (.inr (.inl b) : G.GNode) = y) ∧
    ∀ z ∈ l, z ≠ x → z ≠ y → S.interFam a0 a1 E z

theorem nodup_idx {α : Type*} {l : List α} (h : l.Nodup) {a b : ℕ} {z : α} (ha : l[a]? = some z)
    (hb : l[b]? = some z) : a = b := by
  obtain ⟨ha', hza⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨hb', hzb⟩ := List.getElem?_eq_some_iff.1 hb
  exact (h.getElem_inj).1 (hza.trans hzb.symm)

/-- A family node of `Γ` with a neighbour is a family. -/
theorem gadj_fam_mem {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {x : G.GNode} {Fm : Set G.Block}
    (h : S.gadj a0 a1 Z E x (.inr (.inr Fm))) : Fm ∈ S.families a0 a1 E := by
  rcases h with h | h
  · rcases x with u | b | Fm'
    · obtain ⟨hF, -⟩ := h
      exact hF
    · rcases b with _ | _ <;> simp [gadj0] at h
    · simp [gadj0] at h
  · rcases x with u | b | Fm'
    · simp [gadj0] at h
    · rcases b with _ | _
      · obtain ⟨hF, -⟩ := h
        exact hF
      · obtain ⟨hF, -⟩ := h
        exact hF
    · simp [gadj0] at h

/-- **Lemma C gives the T2 event**: if S3' fails, `T2ev` holds. -/
theorem T2ev_of_fails {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (Z : Solver G) {E : G.Ed → ZMod 2}
    (hfail : failsOn (S3Geom.S3dec S a0 a1 Z) E) : S.T2ev a0 a1 Z E := by
  obtain ⟨L, hh, hl, hnd, hch⟩ := S.lemmaC_path ha0 Z hfail
  have hne : L ≠ [] := by
    rintro rfl
    simp at hh
  have hL0 : L[0]? = some (.inr (.inl false)) := by rw [← List.head?_eq_getElem?]; exact hh
  have hLN : L[L.length - 1]? = some (.inr (.inl true)) := by rw [← List.getLast?_eq_getElem?]; exact hl
  have hN0 : 0 < L.length - 1 := by
    by_contra h0
    have h0' : L.length - 1 = 0 := by omega
    rw [h0', hL0] at hLN
    simp at hLN
  -- the last bottom-strip family node
  let P : ℕ → Prop := fun k => ∃ z, L[k]? = some z ∧ S.botFam a0 a1 E z
  obtain ⟨j0, hj0eq⟩ : ∃ j0, Nat.findGreatest P (L.length - 1) = j0 := ⟨_, rfl⟩
  have hj0N : j0 ≤ L.length - 1 := hj0eq ▸ Nat.findGreatest_le _
  have hj0max : ∀ k, k ≤ L.length - 1 → P k → k ≤ j0 := fun k hk hPk => hj0eq ▸ Nat.le_findGreatest hk hPk
  have hj0P : j0 ≠ 0 → P j0 := fun h => Nat.findGreatest_of_ne_zero hj0eq h
  have hj0lt : j0 < L.length - 1 := by
    rcases eq_or_lt_of_le hj0N with h | h
    · exfalso
      obtain ⟨z, hz, hbot⟩ := hj0P (by omega)
      rw [h, hLN] at hz
      cases hz
      exact hbot
    · exact h
  -- the first top-strip family node after it
  let Q : ℕ → Prop := fun k => k = L.length - 1 ∨ (j0 < k ∧ ∃ z, L[k]? = some z ∧ S.topFam a0 a1 E z)
  have hQex : ∃ k, Q k := ⟨L.length - 1, Or.inl rfl⟩
  obtain ⟨j1, hj1eq⟩ : ∃ j1, Nat.find hQex = j1 := ⟨_, rfl⟩
  have hQj1 : Q j1 := hj1eq ▸ Nat.find_spec hQex
  have hj1min : ∀ k, Q k → j1 ≤ k := fun k hk => hj1eq ▸ Nat.find_min' hQex hk
  have hj1N : j1 ≤ L.length - 1 := hj1min _ (Or.inl rfl)
  have hj01 : j0 < j1 := by
    rcases hQj1 with h | ⟨h, _⟩
    · rw [h]; exact hj0lt
    · exact h
  obtain ⟨x, hx⟩ : ∃ x, L[j0]? = some x := ⟨L[j0], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨y, hy⟩ : ∃ y, L[j1]? = some y := ⟨L[j1], List.getElem?_eq_getElem (by omega)⟩
  have hsub : ∀ i, ((L.drop j0).take (j1 - j0 + 1))[i]? = if i < j1 - j0 + 1 then L[j0 + i]? else none := by
    intro i
    rw [List.getElem?_take, List.getElem?_drop]
  have hlen : ((L.drop j0).take (j1 - j0 + 1)).length = j1 - j0 + 1 := by
    simp only [List.length_take, List.length_drop]
    omega
  refine ⟨(L.drop j0).take (j1 - j0 + 1), x, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, hsub, ite_eq_left (by omega), Nat.add_zero, hx]
  · rw [List.getLast?_eq_getElem?, hlen, hsub, ite_eq_left (by omega), show j0 + (j1 - j0 + 1 - 1) = j1 by omega,
      hy]
  · exact hnd.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  · exact (hch.drop j0).take _
  · by_cases h0 : j0 = 0
    · left
      rw [h0, hL0] at hx
      exact (Option.some.inj hx).symm
    · right
      obtain ⟨z, hz, hbot⟩ := hj0P h0
      rw [hx] at hz
      rw [Option.some.inj hz]
      exact hbot
  · rcases hQj1 with h | ⟨_, z, hz, htop⟩
    · left
      rw [h, hLN] at hy
      exact (Option.some.inj hy).symm
    · right
      rw [hy] at hz
      rw [Option.some.inj hz]
      exact htop
  · -- the boundaries occur only at the ends
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb
    rw [hsub] at hi
    split_ifs at hi with hilt
    rcases b with _ | _
    · left
      have := nodup_idx hnd hi hL0
      have hj0' : j0 = 0 := by omega
      rw [hj0', hL0] at hx
      exact Option.some.inj hx
    · right
      have := nodup_idx hnd hi hLN
      have hj1' : j1 = L.length - 1 := by omega
      rw [hj1', hLN] at hy
      exact Option.some.inj hy
  · intro z hz hzx hzy
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hz
    rw [hsub] at hi
    split_ifs at hi with hilt
    · have hik : i ≠ 0 := by
        rintro rfl
        rw [Nat.add_zero, hx] at hi
        exact hzx (Option.some.inj hi).symm
      have hik2 : j0 + i ≠ j1 := by
        intro h
        rw [h, hy] at hi
        exact hzy (Option.some.inj hi).symm
      rcases z with u | b | Fm
      · trivial
      · trivial
      · -- a family node strictly inside: in `families`, and no strip block
        have hmem : Fm ∈ S.families a0 a1 E := by
          have hk : j0 + i - 1 + 1 < L.length := by omega
          have hc := hch.getElem (j0 + i - 1) hk
          have hi' := hi
          rw [show j0 + i = j0 + i - 1 + 1 by omega, List.getElem?_eq_getElem hk] at hi'
          rw [Option.some.inj hi'] at hc
          exact S.gadj_fam_mem hc
        refine ⟨hmem, fun c hc => ⟨?_, ?_⟩⟩
        · by_contra hle
          push Not at hle
          have hPk : P (j0 + i) := ⟨_, hi, hmem, c, hc, hle⟩
          have := hj0max _ (show j0 + i ≤ L.length - 1 by omega) hPk
          omega
        · by_contra hle
          push Not at hle
          have hQk : Q (j0 + i) := Or.inr ⟨by omega, _, hi, hmem, c, hc, hle⟩
          have := hj1min _ hQk
          omega

/-! ### (R) on a T2 path -/

theorem chain_step {α : Type*} {R : α → α → Prop} {l : List α} (h : List.IsChain R l) {k : ℕ} {a b : α}
    (ha : l[k]? = some a) (hb : l[k + 1]? = some b) : R a b := by
  obtain ⟨hk1, rfl⟩ := List.getElem?_eq_some_iff.1 hb
  obtain ⟨hk0, rfl⟩ := List.getElem?_eq_some_iff.1 ha
  exact h.getElem k hk1

theorem not_gadj_fam_fam {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {Fm Fm' : Set G.Block} :
    ¬ S.gadj a0 a1 Z E (.inr (.inr Fm)) (.inr (.inr Fm')) := by
  rintro (h | h) <;> simp [gadj0] at h

theorem gadj_fam_check {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {Fm : Set G.Block} {u : G.V}
    (h : S.gadj a0 a1 Z E (.inr (.inr Fm)) (.inl u)) :
    Fm ∈ S.families a0 a1 E ∧ G.blockOf u ∈ Fm ∧ S.om a0 a1 E u ≠ 0 := by
  rcases h with h | h
  · simp [gadj0] at h
  · exact h

theorem gadj_check_fam {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {Fm : Set G.Block} {u : G.V}
    (h : S.gadj a0 a1 Z E (.inl u) (.inr (.inr Fm))) :
    Fm ∈ S.families a0 a1 E ∧ G.blockOf u ∈ Fm ∧ S.om a0 a1 E u ≠ 0 := by
  rcases h with h | h
  · exact h
  · simp [gadj0] at h

/-- On a T2 path, a node strictly inside (not at either end) that is not a family node is a check. -/
theorem inner_check {l : List G.GNode} {x y : G.GNode}
    (hhd : l.head? = some x) (hlast : l.getLast? = some y) (hnd : l.Nodup)
    (hbd : ∀ b : Bool, (.inr (.inl b) : G.GNode) ∈ l → (.inr (.inl b) : G.GNode) = x ∨ (.inr (.inl b) : G.GNode) = y)
    {k : ℕ} {z : G.GNode} (hk0 : 0 < k) (hk1 : k + 1 < l.length) (hz : l[k]? = some z)
    (hzf : ∀ F, z ≠ .inr (.inr F)) : ∃ u, z = .inl u := by
  rcases z with u | b | F
  · exact ⟨u, rfl⟩
  · exfalso
    have hmem : (.inr (.inl b) : G.GNode) ∈ l := List.mem_of_getElem? hz
    rcases hbd b hmem with h | h
    · rw [List.head?_eq_getElem?, ← h] at hhd
      have := nodup_idx hnd hz hhd
      omega
    · rw [List.getLast?_eq_getElem?, ← h] at hlast
      have := nodup_idx hnd hz hlast
      omega
  · exact absurd rfl (hzf F)

/-- **(R) on a T2 path**: for two family nodes of a T2 path with no family node between them, the check after the
first and the check before the second lie in blocks more than `a1` apart. -/
theorem path_R {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {l : List G.GNode} {x y : G.GNode}
    (hhd : l.head? = some x) (hlast : l.getLast? = some y) (hnd : l.Nodup)
    (hch : List.IsChain (S.gadj a0 a1 Z E) l)
    (hbd : ∀ b : Bool, (.inr (.inl b) : G.GNode) ∈ l → (.inr (.inl b) : G.GNode) = x ∨ (.inr (.inl b) : G.GNode) = y)
    {i j : ℕ} {Fm Fm' : Set G.Block} (hij : i < j) (hi : l[i]? = some (.inr (.inr Fm)))
    (hj : l[j]? = some (.inr (.inr Fm'))) (hmid : ∀ k, i < k → k < j → ∀ F, l[k]? ≠ some (.inr (.inr F))) :
    ∃ u v : G.V, l[i + 1]? = some (.inl u) ∧ l[j - 1]? = some (.inl v) ∧
      a1 < G.blockDist (G.blockOf u) (G.blockOf v) := by
  obtain ⟨hjl, _⟩ := List.getElem?_eq_some_iff.1 hj
  have hi1 : i + 1 < j := by
    by_contra h
    have hj' : j = i + 1 := by omega
    rw [hj'] at hj
    exact S.not_gadj_fam_fam (chain_step hch hi hj)
  -- the two inner nodes are checks
  obtain ⟨z1, hz1⟩ : ∃ z, l[i + 1]? = some z := ⟨l[i + 1], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨z2, hz2⟩ : ∃ z, l[j - 1]? = some z := ⟨l[j - 1], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨u, rfl⟩ := inner_check hhd hlast hnd hbd (by omega) (by omega) hz1
    (fun F hF => hmid (i + 1) (by omega) (by omega) F (hF ▸ hz1))
  obtain ⟨v, rfl⟩ := inner_check hhd hlast hnd hbd (by omega) (by omega) hz2
    (fun F hF => hmid (j - 1) (by omega) (by omega) F (hF ▸ hz2))
  refine ⟨u, v, hz1, hz2, ?_⟩
  obtain ⟨hFm, hu, hou⟩ := S.gadj_fam_check (chain_step hch hi hz1)
  have hz2' : l[j - 1 + 1]? = some (.inr (.inr Fm')) := by rw [show j - 1 + 1 = j by omega]; exact hj
  obtain ⟨hFm', hv, hov⟩ := S.gadj_check_fam (chain_step hch hz2 hz2')
  refine S.om_far hou hov ?_
  rw [S.family_eq_of_mem_families hFm hu, S.family_eq_of_mem_families hFm' hv]
  intro hFF
  rw [hFF] at hi
  have := nodup_idx hnd hi hj
  omega

/-! ### The `C_top` edges of a T2 path -/

/-- The `C_top` edges carried by a step of `Γ`: a bulk edge between two checks, a half-edge between a check and a
boundary; none at a family node. -/
def stepE (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) : G.GNode → G.GNode → G.Ed → Prop
  | .inl u, .inl w, e => e.ends = {u, w} ∧ u ≠ w ∧ S.ctop a0 a1 Z E e ≠ 0
  | .inl u, .inr (.inl false), e => ∃ x, u = (x, 0) ∧ e = .bot x ∧ S.ctop a0 a1 Z E e ≠ 0
  | .inr (.inl false), .inl u, e => ∃ x, u = (x, 0) ∧ e = .bot x ∧ S.ctop a0 a1 Z E e ≠ 0
  | .inl u, .inr (.inl true), e => ∃ x, u = (x, Fin.last _) ∧ e = .top x ∧ S.ctop a0 a1 Z E e ≠ 0
  | .inr (.inl true), .inl u, e => ∃ x, u = (x, Fin.last _) ∧ e = .top x ∧ S.ctop a0 a1 Z E e ≠ 0
  | _, _, _ => False

/-- The edge of a step (chosen), as an edge set. -/
noncomputable def edgeOf (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) (x y : G.GNode) : G.Ed → ZMod 2 :=
  if h : ∃ e, S.stepE a0 a1 Z E x y e then Pi.single (Classical.choose h) 1 else 0

/-- The node at position `k` (a default beyond the end). -/
def nd (l : List G.GNode) (k : ℕ) : G.GNode := (l[k]?).getD (.inr (.inl false))

/-- **The `C_top` paths of a T2 path**: the edges of all its steps. -/
noncomputable def Pl (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) (l : List G.GNode) : G.Ed → ZMod 2 :=
  ∑ k ∈ Finset.range (l.length - 1), S.edgeOf a0 a1 Z E (nd l k) (nd l (k + 1))

/-- The syndrome of a single check (zero at other nodes). -/
noncomputable def sOf : G.GNode → G.V → ZMod 2
  | .inl u => Pi.single u 1
  | _ => 0

/-- The node is a family node. -/
def isFam (z : G.GNode) : Prop := ∃ F, z = .inr (.inr F)

theorem sOf_of_not_check {z : G.GNode} (hz : ∀ u, z ≠ .inl u) : sOf z = 0 := by
  rcases z with u | b | F
  · exact absurd rfl (hz u)
  · rfl
  · rfl

theorem stepE_ctop {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {x y : G.GNode} {e : G.Ed}
    (h : S.stepE a0 a1 Z E x y e) : S.ctop a0 a1 Z E e ≠ 0 := by
  rcases x with u | (_ | _) | F <;> rcases y with w | (_ | _) | F' <;> simp only [stepE] at h
  · exact h.2.2
  · obtain ⟨_, _, _, h⟩ := h; exact h
  · obtain ⟨_, _, _, h⟩ := h; exact h
  · obtain ⟨_, _, _, h⟩ := h; exact h
  · obtain ⟨_, _, _, h⟩ := h; exact h

/-- **The C_top paths lie in `C_top`.** -/
theorem Pl_subset {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} (l : List G.GNode) (e : G.Ed)
    (he : S.Pl a0 a1 Z E l e ≠ 0) : S.ctop a0 a1 Z E e ≠ 0 := by
  unfold Pl at he
  rw [Finset.sum_apply] at he
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  unfold edgeOf at hk
  split_ifs at hk with h
  · have he' : e = Classical.choose h := by
      by_contra hne
      exact hk (by simp [hne])
    rw [he']
    exact S.stepE_ctop (Classical.choose_spec h)
  · exact absurd rfl hk

theorem psyn_single (e : G.Ed) (v : G.V) :
    psyn G.w G.h (Pi.single e 1) v = if v ∈ e.ends then 1 else 0 := by
  rw [psyn_apply, Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    simp [hfe]
  · simp

/-- The syndrome of the edge of a step of `Γ`. -/
theorem psyn_edgeOf {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {x y : G.GNode}
    (hxy : S.gadj a0 a1 Z E x y) :
    psyn G.w G.h (S.edgeOf a0 a1 Z E x y) = if isFam x ∨ isFam y then 0 else sOf x + sOf y := by
  -- the step's edge, when the step carries one
  have hsingle : ∀ (h : ∃ e, S.stepE a0 a1 Z E x y e),
      psyn G.w G.h (S.edgeOf a0 a1 Z E x y) = psyn G.w G.h (Pi.single (Classical.choose h) 1) := by
    intro h
    unfold edgeOf
    rw [dite_eq_left h]
  rcases x with u | (_ | _) | F <;> rcases y with w | (_ | _) | F'
  -- two checks
  · have h : ∃ e, S.stepE a0 a1 Z E (.inl u) (.inl w) e := by
      rcases hxy with ⟨e, he, hne, hc⟩ | ⟨e, he, hne, hc⟩
      · exact ⟨e, he, hne, hc⟩
      · exact ⟨e, by rw [he, Finset.pair_comm], hne.symm, hc⟩
    rw [hsingle h]
    obtain ⟨hends, hne, _⟩ := Classical.choose_spec h
    have hnf : ¬ (isFam (.inl u : G.GNode) ∨ isFam (.inl w : G.GNode)) := by
      rintro (⟨F, hF⟩ | ⟨F, hF⟩) <;> cases hF
    rw [ite_eq_right hnf]
    funext v
    rw [psyn_single, hends]
    simp only [sOf, Pi.add_apply, Pi.single_apply, Finset.mem_insert, Finset.mem_singleton]
    by_cases hvu : v = u <;> by_cases hvw : v = w
    · exact absurd (hvu.symm.trans hvw) hne
    · subst hvu
      simp [hne]
    · subst hvw
      simp [hne.symm]
    · simp [hvu, hvw]
  -- check and b₁
  · have h : ∃ e, S.stepE a0 a1 Z E (.inl u) (.inr (.inl false)) e := by
      rcases hxy with ⟨x, hx, hc⟩ | h
      · exact ⟨_, x, hx, rfl, hc⟩
      · simp [gadj0] at h
    rw [hsingle h]
    obtain ⟨x, hx, hex, _⟩ := Classical.choose_spec h
    have hnf : ¬ (isFam (.inl u : G.GNode) ∨ isFam (.inr (.inl false) : G.GNode)) := by
      rintro (⟨F, hF⟩ | ⟨F, hF⟩) <;> cases hF
    rw [ite_eq_right hnf, hex]
    funext v
    rw [psyn_single, hx]
    simp [sOf, PEdge.ends, Pi.single_apply]
  -- check and b₂
  · have h : ∃ e, S.stepE a0 a1 Z E (.inl u) (.inr (.inl true)) e := by
      rcases hxy with ⟨x, hx, hc⟩ | h
      · exact ⟨_, x, hx, rfl, hc⟩
      · simp [gadj0] at h
    rw [hsingle h]
    obtain ⟨x, hx, hex, _⟩ := Classical.choose_spec h
    have hnf : ¬ (isFam (.inl u : G.GNode) ∨ isFam (.inr (.inl true) : G.GNode)) := by
      rintro (⟨F, hF⟩ | ⟨F, hF⟩) <;> cases hF
    rw [ite_eq_right hnf, hex]
    funext v
    rw [psyn_single, hx]
    simp [sOf, PEdge.ends, Pi.single_apply]
  -- check and family
  · have hf : isFam (.inl u : G.GNode) ∨ isFam (.inr (.inr F') : G.GNode) := Or.inr ⟨F', rfl⟩
    rw [ite_eq_left hf]
    unfold edgeOf
    rw [dite_eq_right (by rintro ⟨e, he⟩; simp [stepE] at he), map_zero]
  -- b₁ and check
  · have h : ∃ e, S.stepE a0 a1 Z E (.inr (.inl false)) (.inl w) e := by
      rcases hxy with h | ⟨x, hx, hc⟩
      · simp [gadj0] at h
      · exact ⟨_, x, hx, rfl, hc⟩
    rw [hsingle h]
    obtain ⟨x, hx, hex, _⟩ := Classical.choose_spec h
    have hnf : ¬ (isFam (.inr (.inl false) : G.GNode) ∨ isFam (.inl w : G.GNode)) := by
      rintro (⟨F, hF⟩ | ⟨F, hF⟩) <;> cases hF
    rw [ite_eq_right hnf, hex]
    funext v
    rw [psyn_single, hx]
    simp [sOf, PEdge.ends, Pi.single_apply]
  -- boundary to boundary: no step
  · rcases hxy with h | h <;> simp [gadj0] at h
  · rcases hxy with h | h <;> simp [gadj0] at h
  · have hf : isFam (.inr (.inl false) : G.GNode) ∨ isFam (.inr (.inr F') : G.GNode) := Or.inr ⟨F', rfl⟩
    rw [ite_eq_left hf]
    unfold edgeOf
    rw [dite_eq_right (by rintro ⟨e, he⟩; simp [stepE] at he), map_zero]
  -- b₂ and check
  · have h : ∃ e, S.stepE a0 a1 Z E (.inr (.inl true)) (.inl w) e := by
      rcases hxy with h | ⟨x, hx, hc⟩
      · simp [gadj0] at h
      · exact ⟨_, x, hx, rfl, hc⟩
    rw [hsingle h]
    obtain ⟨x, hx, hex, _⟩ := Classical.choose_spec h
    have hnf : ¬ (isFam (.inr (.inl true) : G.GNode) ∨ isFam (.inl w : G.GNode)) := by
      rintro (⟨F, hF⟩ | ⟨F, hF⟩) <;> cases hF
    rw [ite_eq_right hnf, hex]
    funext v
    rw [psyn_single, hx]
    simp [sOf, PEdge.ends, Pi.single_apply]
  · rcases hxy with h | h <;> simp [gadj0] at h
  · rcases hxy with h | h <;> simp [gadj0] at h
  · have hf : isFam (.inr (.inl true) : G.GNode) ∨ isFam (.inr (.inr F') : G.GNode) := Or.inr ⟨F', rfl⟩
    rw [ite_eq_left hf]
    unfold edgeOf
    rw [dite_eq_right (by rintro ⟨e, he⟩; simp [stepE] at he), map_zero]
  -- a family first
  · have hf : isFam (.inr (.inr F) : G.GNode) ∨ isFam (.inl w : G.GNode) := Or.inl ⟨F, rfl⟩
    rw [ite_eq_left hf]
    unfold edgeOf
    rw [dite_eq_right (by rintro ⟨e, he⟩; simp [stepE] at he), map_zero]
  · have hf : isFam (.inr (.inr F) : G.GNode) ∨ isFam (.inr (.inl false) : G.GNode) := Or.inl ⟨F, rfl⟩
    rw [ite_eq_left hf]
    unfold edgeOf
    rw [dite_eq_right (by rintro ⟨e, he⟩; simp [stepE] at he), map_zero]
  · have hf : isFam (.inr (.inr F) : G.GNode) ∨ isFam (.inr (.inl true) : G.GNode) := Or.inl ⟨F, rfl⟩
    rw [ite_eq_left hf]
    unfold edgeOf
    rw [dite_eq_right (by rintro ⟨e, he⟩; simp [stepE] at he), map_zero]
  · have hf : isFam (.inr (.inr F) : G.GNode) ∨ isFam (.inr (.inr F') : G.GNode) := Or.inl ⟨F, rfl⟩
    rw [ite_eq_left hf]
    unfold edgeOf
    rw [dite_eq_right (by rintro ⟨e, he⟩; simp [stepE] at he), map_zero]

/-- The odd checks contributed by the node at position `k` of `l` (for a family node): its neighbouring checks. -/
noncomputable def stT (l : List G.GNode) (k : ℕ) : G.V → ZMod 2 :=
  (if 0 < k then sOf (nd l (k - 1)) else 0) + (if k + 1 < l.length then sOf (nd l (k + 1)) else 0)

theorem telescope (f : ℕ → G.V → ZMod 2) (m : ℕ) :
    ∑ j ∈ Finset.range m, (f j + f (j + 1)) = f 0 + f m := by
  induction m with
  | zero =>
    funext v
    simp only [Finset.range_zero, Finset.sum_empty, Pi.zero_apply, Pi.add_apply]
    exact (zmod2_add_self _).symm
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    funext v
    simp only [Pi.add_apply]
    linear_combination zmod2_add_self (f m v)

theorem sOf_fam {z : G.GNode} (hz : isFam z) : sOf z = 0 := by
  obtain ⟨F, rfl⟩ := hz
  rfl

theorem nd_of_getElem? {l : List G.GNode} {k : ℕ} {z : G.GNode} (h : l[k]? = some z) : nd l k = z := by
  simp [nd, h]

theorem fun_add_self (x : G.V → ZMod 2) : x + x = 0 := by
  funext v
  exact zmod2_add_self _

/-- **The odd checks of the C_top paths of a `Γ`-chain**: the checks next to its family nodes, plus its end nodes if
they are checks. -/
theorem psyn_Pl {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {l : List G.GNode}
    (hch : List.IsChain (S.gadj a0 a1 Z E) l) (hl : l ≠ []) :
    psyn G.w G.h (S.Pl a0 a1 Z E l) =
      (∑ k ∈ Finset.range l.length, if isFam (nd l k) then stT l k else 0) + sOf (nd l 0) +
        sOf (nd l (l.length - 1)) := by
  have hn : 1 ≤ l.length := List.length_pos_of_ne_nil hl
  obtain ⟨m, hm⟩ : ∃ m, l.length = m + 1 := ⟨l.length - 1, by omega⟩
  -- the steps' syndromes
  have hstep : ∀ j ∈ Finset.range m, psyn G.w G.h (S.edgeOf a0 a1 Z E (nd l j) (nd l (j + 1))) =
      if isFam (nd l j) ∨ isFam (nd l (j + 1)) then 0 else sOf (nd l j) + sOf (nd l (j + 1)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj1 : j < l.length := by omega
    have hj2 : j + 1 < l.length := by omega
    have e1 : l[j]? = some (nd l j) := by simp [nd, List.getElem?_eq_getElem hj1]
    have e2 : l[j + 1]? = some (nd l (j + 1)) := by simp [nd, List.getElem?_eq_getElem hj2]
    exact S.psyn_edgeOf (chain_step hch e1 e2)
  -- the station sum, by steps
  have hst : (∑ k ∈ Finset.range l.length, if isFam (nd l k) then stT l k else 0) =
      ∑ j ∈ Finset.range m, ((if isFam (nd l (j + 1)) then sOf (nd l j) else 0) +
        (if isFam (nd l j) then sOf (nd l (j + 1)) else 0)) := by
    have hsplit : ∀ k, (if isFam (nd l k) then stT l k else 0) =
        (if isFam (nd l k) then (if 0 < k then sOf (nd l (k - 1)) else 0) else 0) +
          (if isFam (nd l k) then (if k + 1 < l.length then sOf (nd l (k + 1)) else 0) else 0) := by
      intro k
      unfold stT
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_add_distrib, hm,
      Finset.sum_range_succ', Finset.sum_range_succ]
    have h0 : (if isFam (nd l 0) then (if 0 < 0 then sOf (nd l (0 - 1)) else 0) else 0) = 0 := by simp
    have hlast : (if isFam (nd l m) then (if m + 1 < m + 1 then sOf (nd l (m + 1)) else 0) else 0) = 0 := by
      simp
    rw [h0, hlast, add_zero, add_zero]
    have h1 : ∀ j ∈ Finset.range m, (if isFam (nd l (j + 1)) then (if 0 < j + 1 then sOf (nd l (j + 1 - 1)) else 0)
        else 0) = if isFam (nd l (j + 1)) then sOf (nd l j) else 0 := fun j _ => by simp
    have h2 : ∀ j ∈ Finset.range m, (if isFam (nd l j) then (if j + 1 < m + 1 then sOf (nd l (j + 1)) else 0)
        else 0) = if isFam (nd l j) then sOf (nd l (j + 1)) else 0 := fun j hj => by
      rw [Finset.mem_range] at hj
      have : j + 1 < m + 1 := by omega
      simp [this]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  rw [hst]
  have hpt : ∀ j, (if isFam (nd l j) ∨ isFam (nd l (j + 1)) then 0 else sOf (nd l j) + sOf (nd l (j + 1))) +
      ((if isFam (nd l (j + 1)) then sOf (nd l j) else 0) + (if isFam (nd l j) then sOf (nd l (j + 1)) else 0)) =
      sOf (nd l j) + sOf (nd l (j + 1)) := by
    intro j
    by_cases h1 : isFam (nd l j) <;> by_cases h2 : isFam (nd l (j + 1))
    · simp [h1, h2, sOf_fam h1, sOf_fam h2]
    · simp [h1, h2, sOf_fam h1]
    · simp [h1, h2, sOf_fam h2]
    · simp [h1, h2]
  have htot : psyn G.w G.h (S.Pl a0 a1 Z E l) + ∑ j ∈ Finset.range m,
      ((if isFam (nd l (j + 1)) then sOf (nd l j) else 0) + (if isFam (nd l j) then sOf (nd l (j + 1)) else 0)) =
      sOf (nd l 0) + sOf (nd l m) := by
    unfold Pl
    rw [map_sum, hm, Nat.add_sub_cancel, Finset.sum_congr rfl hstep, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun j _ => hpt j, telescope (fun j => sOf (nd l j)) m]
  rw [hm, Nat.add_sub_cancel]
  set B := ∑ j ∈ Finset.range m,
    ((if isFam (nd l (j + 1)) then sOf (nd l j) else 0) + (if isFam (nd l j) then sOf (nd l (j + 1)) else 0))
  calc psyn G.w G.h (S.Pl a0 a1 Z E l) = psyn G.w G.h (S.Pl a0 a1 Z E l) + (B + B) := by
        rw [fun_add_self, add_zero]
    _ = (psyn G.w G.h (S.Pl a0 a1 Z E l) + B) + B := by rw [add_assoc]
    _ = (sOf (nd l 0) + sOf (nd l m)) + B := by rw [htot]
    _ = B + sOf (nd l 0) + sOf (nd l m) := by abel

end Stage1

/-! ### Pair costs and (X) -/

namespace S3Geom

variable {G : S3Geom}

/-- The minimum weight of an edge set with odd checks `T` (the pair cost of `T`). -/
noncomputable def pairCost (wt : G.Ed → ℝ) (T : G.V → ZMod 2) : ℝ :=
  if h : (Finset.univ.filter (fun X : G.Ed → ZMod 2 => psyn G.w G.h X = T)).Nonempty then
    (Finset.univ.filter (fun X : G.Ed → ZMod 2 => psyn G.w G.h X = T)).inf' h (wsum wt) else 0

theorem psyn_surj (T : G.V → ZMod 2) : ∃ X : G.Ed → ZMod 2, psyn G.w G.h X = T := by
  obtain ⟨X, _, hX⟩ := realizable_of_rough conn_univ (Set.mem_univ (⟨0, by omega⟩, ⟨0, by omega⟩)) (Or.inl rfl)
    (T := T) (fun v _ => Set.mem_univ v)
  exact ⟨X, hX⟩

theorem pairCost_le {wt : G.Ed → ℝ} {T : G.V → ZMod 2} {X : G.Ed → ZMod 2} (hX : psyn G.w G.h X = T) :
    pairCost wt T ≤ wsum wt X := by
  have h : (Finset.univ.filter (fun X : G.Ed → ZMod 2 => psyn G.w G.h X = T)).Nonempty := ⟨X, by simp [hX]⟩
  unfold pairCost
  rw [dite_eq_left h]
  exact Finset.inf'_le _ (by simp [hX])

theorem exists_pairCost (wt : G.Ed → ℝ) (T : G.V → ZMod 2) :
    ∃ X : G.Ed → ZMod 2, psyn G.w G.h X = T ∧ wsum wt X = pairCost wt T := by
  obtain ⟨X0, hX0⟩ := psyn_surj T
  have h : (Finset.univ.filter (fun X : G.Ed → ZMod 2 => psyn G.w G.h X = T)).Nonempty := ⟨X0, by simp [hX0]⟩
  obtain ⟨X, hXmem, hXeq⟩ := Finset.exists_mem_eq_inf' h (wsum wt)
  refine ⟨X, (Finset.mem_filter.1 hXmem).2, ?_⟩
  unfold pairCost
  rw [dite_eq_left h, hXeq]

theorem wsum_nonneg {wt : G.Ed → ℝ} (hwt : ∀ e, 0 ≤ wt e) (X : G.Ed → ZMod 2) : 0 ≤ wsum wt X :=
  Finset.sum_nonneg fun e _ => by
    split_ifs
    · exact hwt e
    · exact le_rfl

theorem pairCost_nonneg {wt : G.Ed → ℝ} (hwt : ∀ e, 0 ≤ wt e) (T : G.V → ZMod 2) : 0 ≤ pairCost wt T := by
  obtain ⟨X, -, hX⟩ := exists_pairCost wt T
  rw [← hX]
  exact wsum_nonneg hwt X

theorem pairCost_zero {wt : G.Ed → ℝ} (hwt : ∀ e, 0 ≤ wt e) : pairCost wt (0 : G.V → ZMod 2) = 0 := by
  refine le_antisymm ?_ (pairCost_nonneg hwt 0)
  have h := pairCost_le (wt := wt) (X := (0 : G.Ed → ZMod 2)) (map_zero _)
  simpa [wsum] using h

theorem pairCost_add_le {wt : G.Ed → ℝ} (hwt : ∀ e, 0 ≤ wt e) (T T' : G.V → ZMod 2) :
    pairCost wt (T + T') ≤ pairCost wt T + pairCost wt T' := by
  obtain ⟨X, hX, hXc⟩ := exists_pairCost wt T
  obtain ⟨X', hX', hXc'⟩ := exists_pairCost wt T'
  calc pairCost wt (T + T') ≤ wsum wt (X + X') := pairCost_le (by rw [map_add, hX, hX'])
    _ ≤ wsum wt X + wsum wt X' := wsum_add_le hwt X X'
    _ = pairCost wt T + pairCost wt T' := by rw [hXc, hXc']

theorem pairCost_sum_le {wt : G.Ed → ℝ} (hwt : ∀ e, 0 ≤ wt e) {ι : Type*} (s : Finset ι) (T : ι → G.V → ZMod 2) :
    pairCost wt (∑ i ∈ s, T i) ≤ ∑ i ∈ s, pairCost wt (T i) := by
  induction s using Finset.induction_on with
  | empty => simp [pairCost_zero hwt]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (pairCost_add_le hwt _ _).trans (add_le_add le_rfl ih)

end S3Geom

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- **(X), general form, on a `Γ`-chain**: the C_top paths weigh at most any edge set with the same odd checks. -/
theorem path_X {a0 a1 : ℕ} (Z : Solver G) (hwt : ∀ e, 0 ≤ Z.wt e) {E : G.Ed → ZMod 2} (l : List G.GNode)
    {P' : G.Ed → ZMod 2} (hP' : psyn G.w G.h P' = psyn G.w G.h (S.Pl a0 a1 Z E l)) :
    S3Geom.wsum Z.wt (S.Pl a0 a1 Z E l) ≤ S3Geom.wsum Z.wt P' :=
  S3Geom.exchange Z hwt (fun e he => S.Pl_subset l e he) hP' (S.psyn_ctop a0 a1 Z E)

/-- **(X) with pair costs, on a `Γ`-chain whose end nodes are not checks**: the C_top paths weigh at
most the sum, over the family nodes of the chain, of the pair cost of their neighbouring checks (entry and exit; for
an end family only one of them, paired with the boundary). -/
theorem path_X_pairs {a0 a1 : ℕ} (Z : Solver G) (hwt : ∀ e, 0 ≤ Z.wt e) {E : G.Ed → ZMod 2} {l : List G.GNode}
    (hch : List.IsChain (S.gadj a0 a1 Z E) l) (hl : l ≠ []) (h0 : ∀ u, nd l 0 ≠ .inl u)
    (hlast : ∀ u, nd l (l.length - 1) ≠ .inl u) :
    S3Geom.wsum Z.wt (S.Pl a0 a1 Z E l) ≤
      ∑ k ∈ Finset.range l.length, if isFam (nd l k) then S3Geom.pairCost Z.wt (stT l k) else 0 := by
  obtain ⟨X, hX, hXc⟩ := S3Geom.exists_pairCost Z.wt (psyn G.w G.h (S.Pl a0 a1 Z E l))
  have hpsyn := S.psyn_Pl hch hl
  rw [sOf_of_not_check h0, sOf_of_not_check hlast, add_zero, add_zero] at hpsyn
  calc S3Geom.wsum Z.wt (S.Pl a0 a1 Z E l) ≤ S3Geom.wsum Z.wt X := S.path_X Z hwt l hX
    _ = S3Geom.pairCost Z.wt (psyn G.w G.h (S.Pl a0 a1 Z E l)) := hXc
    _ = S3Geom.pairCost Z.wt (∑ k ∈ Finset.range l.length, if isFam (nd l k) then stT l k else 0) := by
        rw [hpsyn]
    _ ≤ ∑ k ∈ Finset.range l.length, S3Geom.pairCost Z.wt (if isFam (nd l k) then stT l k else 0) :=
        S3Geom.pairCost_sum_le hwt _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs
        · rfl
        · exact S3Geom.pairCost_zero hwt

/-- **(X) on the T2 event**: for the T2 path of `T2ev` (its ends are `b₁`/`b₂` or family nodes). -/
theorem T2ev_X {a0 a1 : ℕ} (Z : Solver G) (hwt : ∀ e, 0 ≤ Z.wt e) {E : G.Ed → ZMod 2} {l : List G.GNode}
    {x y : G.GNode} (hhd : l.head? = some x) (hlst : l.getLast? = some y)
    (hch : List.IsChain (S.gadj a0 a1 Z E) l)
    (hx : x = .inr (.inl false) ∨ S.botFam a0 a1 E x) (hy : y = .inr (.inl true) ∨ S.topFam a0 a1 E y) :
    S3Geom.wsum Z.wt (S.Pl a0 a1 Z E l) ≤
      ∑ k ∈ Finset.range l.length, if isFam (nd l k) then S3Geom.pairCost Z.wt (stT l k) else 0 := by
  have hl : l ≠ [] := by
    rintro rfl
    simp at hhd
  have hnd0 : nd l 0 = x := nd_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd)
  have hndl : nd l (l.length - 1) = y := nd_of_getElem? (by rw [← List.getLast?_eq_getElem?]; exact hlst)
  refine S.path_X_pairs Z hwt hch hl ?_ ?_
  · intro u hu
    rw [hnd0] at hu
    subst hu
    rcases hx with h | h
    · cases h
    · exact h
  · intro u hu
    rw [hndl] at hu
    subst hu
    rcases hy with h | h
    · cases h
    · exact h

end Stage1

namespace S3Fam

variable (fam : S3Fam)

/-- **H2D_T2ev** (named hypothesis; the T2 bound for the T2 event): on every code with `n_x ≥ 5` and
`n_y ≥ nyMin`, Hypothesis (H) implies `P(T2ev ∧ ¬T1) ≤ C2 n_x e^{-s2 (n_y - H0)}`. -/
def H2D_T2ev (a0 a1 : ℕ) (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny))
    (K : BoundConsts) (q ε : ℝ) : Prop :=
  ∀ (nx ny : ℕ) (hnx : 5 ≤ nx) (hny : K.nyMin ≤ ny) (hny1 : 1 ≤ ny),
    (fam.stage1 nx ny (by omega) hny1).HypH q ε →
      prob (bernProd q) (fun E => (fam.stage1 nx ny (by omega) hny1).T2ev a0 a1 (Z nx ny (by omega) hny1) E ∧
          ¬ (fam.stage1 nx ny (by omega) hny1).T1 a0 a1 E) ≤
        K.C2 * nx * Real.exp (-K.s2 * ((ny : ℝ) - K.H0))

/-- **The T2 term from the T2 event**: `H2D_T2ev ⟹ H2D_T2` (Lemma C: failure gives the T2 event). -/
theorem h2dT2_of_T2ev {a0 a1 : ℕ} (ha0 : 2 ≤ a0)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny)) (K : BoundConsts)
    {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h : fam.H2D_T2ev a0 a1 Z K q ε) : fam.H2D_T2 a0 a1 Z K q ε := by
  intro nx ny hnx hny hny1 hH
  refine le_trans (prob_mono (bernProd_nonneg hq0 hq1) fun E hE => ⟨?_, hE.2⟩) (h nx ny hnx hny hny1 hH)
  have hfail := hE.1
  unfold S3decFam at hfail
  rw [dite_eq_left (⟨by omega, hny1⟩ : 1 ≤ nx ∧ 1 ≤ ny)] at hfail
  exact (fam.stage1 nx ny (by omega) hny1).T2ev_of_fails ha0 _ hfail

end S3Fam

/-- **Theorem B (a1 = 12 constants), the 2D lemma entering only through its T2 event.** -/
theorem theoremB_a12_T2ev (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hT2 : (sp.toFam hV6).H2D_T2ev 4 12 Z constsA12 0.100 5e-4)
    (htype : (sp.toFam hV6).Htype 0.100) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        9.61e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.0351 * ((nyOf sp.L H : ℝ) - 31)) :=
  theoremB_a12_T2 sp hV6 hR hL2 Z
    ((sp.toFam hV6).h2dT2_of_T2ev (by norm_num) Z constsA12 (by norm_num) (by norm_num) hT2) htype hstat hq hW hH

end QECML
