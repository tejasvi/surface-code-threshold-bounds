import QECD1.LemmaX3

/-!
# The T2 event on the 3D code

The 3D analogue of the first part of the 2D `TwoD/T2Path`. The strips are in the rough direction `y`: block rows
`≤ hs3` (bottom) and `≥ n_y - 1 - hs3` (top).

* `T2ev3`: a simple path of `Γ` that starts at `b₁` or at a bottom-strip family node, ends at `b₂` or at a top-strip
  family node, passes through the boundaries only at its ends, and whose other family nodes are intermediate (no
  block in either strip).
* `T2ev_of_fails3`: if the decoder fails, `T2ev3` holds. Cut the simple path of `lemmaC3_path` at the last
  bottom-strip family node and at the first top-strip family node after it.
* `path_R3` ((R) on a T2 path): for two family nodes with no family node between them, the check after the first and
  the check before the second lie in blocks more than `a1` apart (`om_far3`).
-/

open Finset

namespace QECD1

open Classical

variable {T w h : ℕ}

theorem nodup_idx {α : Type} {l : List α} (hl : l.Nodup) {a b : ℕ} {z : α} (ha : l[a]? = some z)
    (hb : l[b]? = some z) : a = b := by
  obtain ⟨ha', hza⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨hb', hzb⟩ := List.getElem?_eq_some_iff.1 hb
  exact (hl.getElem_inj).1 (hza.trans hzb.symm)

theorem chain_step {α : Type} {R : α → α → Prop} {l : List α} (hl : List.IsChain R l) {k : ℕ} {a b : α}
    (ha : l[k]? = some a) (hb : l[k + 1]? = some b) : R a b := by
  obtain ⟨hk1, rfl⟩ := List.getElem?_eq_some_iff.1 hb
  obtain ⟨hk0, rfl⟩ := List.getElem?_eq_some_iff.1 ha
  exact hl.getElem k hk1

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- A family node whose family has a block in the bottom strip. -/
def botFam3 (ny : ℕ) (E : PEdge3 T w h → ZMod 2) : GNode3 T w h → Prop
  | .inr (.inr Fm) => Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧ ∃ c ∈ Fm, c.2.2 ≤ hs3
  | _ => False

/-- A family node whose family has a block in the top strip. -/
def topFam3 (ny : ℕ) (E : PEdge3 T w h → ZMod 2) : GNode3 T w h → Prop
  | .inr (.inr Fm) => Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧
      ∃ c ∈ Fm, (ny : ℤ) ≤ c.2.2 + 1 + hs3
  | _ => False

/-- An intermediate node: a check, a boundary, or a family with no block in either strip. -/
def interFam3 (ny : ℕ) (E : PEdge3 T w h → ZMod 2) : GNode3 T w h → Prop
  | .inr (.inr Fm) => Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧
      ∀ c ∈ Fm, (hs3 : ℤ) < c.2.2 ∧ c.2.2 + 1 + hs3 < ny
  | _ => True

/-- **The T2 event** (path form): a simple path of `Γ` from `x` (`b₁` or a bottom-strip family node) to `y` (`b₂` or a
top-strip family node), passing through the boundaries only at its ends, whose other family nodes are intermediate. -/
def T2ev3 (ny : ℕ) (E : PEdge3 T w h → ZMod 2) : Prop :=
  ∃ (l : List (GNode3 T w h)) (x y : GNode3 T w h), l.head? = some x ∧ l.getLast? = some y ∧ l.Nodup ∧
    List.IsChain (S.gadj3 Z ny E) l ∧
    (x = .inr (.inl false) ∨ S.botFam3 ny E x) ∧ (y = .inr (.inl true) ∨ S.topFam3 ny E y) ∧
    (∀ b : Bool, (.inr (.inl b) : GNode3 T w h) ∈ l →
      (.inr (.inl b) : GNode3 T w h) = x ∨ (.inr (.inl b) : GNode3 T w h) = y) ∧
    ∀ z ∈ l, z ≠ x → z ≠ y → S.interFam3 ny E z

/-- A family node of `Γ` with a neighbour is a family. -/
theorem gadj_fam_mem3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {x : GNode3 T w h} {Fm : Finset V3}
    (hx : S.gadj3 Z ny E x (.inr (.inr Fm))) : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) := by
  rcases hx with hx | hx
  · rcases x with u | b | Fm'
    · exact hx.1
    · rcases b with _ | _ <;> simp [gadj0] at hx
    · simp [gadj0] at hx
  · rcases x with u | b | Fm'
    · simp [gadj0] at hx
    · rcases b with _ | _
      · exact hx.1
      · exact hx.1
    · simp [gadj0] at hx

/-- **Lemma C gives the T2 event**: if the decoder fails, `T2ev3` holds. -/
theorem T2ev_of_fails3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} (hfail : failsOn3 (dec3 S Z) E) : S.T2ev3 Z ny E := by
  obtain ⟨L, hh, hl, hnd, hch⟩ := S.lemmaC3_path Z (ny := ny) hfail
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
  let P : ℕ → Prop := fun k => ∃ z, L[k]? = some z ∧ S.botFam3 ny E z
  obtain ⟨j0, hj0eq⟩ : ∃ j0, Nat.findGreatest P (L.length - 1) = j0 := ⟨_, rfl⟩
  have hj0N : j0 ≤ L.length - 1 := hj0eq ▸ Nat.findGreatest_le _
  have hj0max : ∀ k, k ≤ L.length - 1 → P k → k ≤ j0 := fun k hk hPk => hj0eq ▸ Nat.le_findGreatest hk hPk
  have hj0P : j0 ≠ 0 → P j0 := fun hj => Nat.findGreatest_of_ne_zero hj0eq hj
  have hj0lt : j0 < L.length - 1 := by
    rcases eq_or_lt_of_le hj0N with hj | hj
    · exfalso
      obtain ⟨z, hz, hbot⟩ := hj0P (by omega)
      rw [hj, hLN] at hz
      cases hz
      exact hbot
    · exact hj
  -- the first top-strip family node after it
  let Q : ℕ → Prop := fun k => k = L.length - 1 ∨ (j0 < k ∧ ∃ z, L[k]? = some z ∧ S.topFam3 ny E z)
  have hQex : ∃ k, Q k := ⟨L.length - 1, Or.inl rfl⟩
  obtain ⟨j1, hj1eq⟩ : ∃ j1, Nat.find hQex = j1 := ⟨_, rfl⟩
  have hQj1 : Q j1 := hj1eq ▸ Nat.find_spec hQex
  have hj1min : ∀ k, Q k → j1 ≤ k := fun k hk => hj1eq ▸ Nat.find_min' hQex hk
  have hj1N : j1 ≤ L.length - 1 := hj1min _ (Or.inl rfl)
  have hj01 : j0 < j1 := by
    rcases hQj1 with hj | ⟨hj, _⟩
    · rw [hj]; exact hj0lt
    · exact hj
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
  · rcases hQj1 with hj | ⟨_, z, hz, htop⟩
    · left
      rw [hj, hLN] at hy
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
        intro hj
        rw [hj, hy] at hi
        exact hzy (Option.some.inj hi).symm
      rcases z with u | b | Fm
      · trivial
      · trivial
      · -- a family node strictly inside: a family, and no strip block
        have hmem : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) := by
          have hk : j0 + i - 1 + 1 < L.length := by omega
          have hc := hch.getElem (j0 + i - 1) hk
          have hi' := hi
          rw [show j0 + i = j0 + i - 1 + 1 by omega, List.getElem?_eq_getElem hk] at hi'
          rw [Option.some.inj hi'] at hc
          exact S.gadj_fam_mem3 Z hc
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

theorem not_gadj_fam_fam3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {Fm Fm' : Finset V3} :
    ¬ S.gadj3 Z ny E (.inr (.inr Fm)) (.inr (.inr Fm')) := by
  rintro (hx | hx) <;> simp [gadj0] at hx

theorem gadj_fam_check3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3} {u : PVert3 T w h}
    (hx : S.gadj3 Z ny E (.inr (.inr Fm)) (.inl u)) :
    Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧ blockOf3 u ∈ Fm ∧ S.om3 E u ≠ 0 := by
  rcases hx with hx | hx
  · simp [gadj0] at hx
  · exact hx

theorem gadj_check_fam3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3} {u : PVert3 T w h}
    (hx : S.gadj3 Z ny E (.inl u) (.inr (.inr Fm))) :
    Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧ blockOf3 u ∈ Fm ∧ S.om3 E u ≠ 0 := by
  rcases hx with hx | hx
  · exact hx
  · simp [gadj0] at hx

end Stage13

/-- On a T2 path, a node strictly inside (not at either end) that is not a family node is a check. -/
theorem inner_check3 {l : List (GNode3 T w h)} {x y : GNode3 T w h}
    (hhd : l.head? = some x) (hlast : l.getLast? = some y) (hnd : l.Nodup)
    (hbd : ∀ b : Bool, (.inr (.inl b) : GNode3 T w h) ∈ l →
      (.inr (.inl b) : GNode3 T w h) = x ∨ (.inr (.inl b) : GNode3 T w h) = y)
    {k : ℕ} {z : GNode3 T w h} (hk0 : 0 < k) (hk1 : k + 1 < l.length) (hz : l[k]? = some z)
    (hzf : ∀ F, z ≠ .inr (.inr F)) : ∃ u, z = .inl u := by
  rcases z with u | b | F
  · exact ⟨u, rfl⟩
  · exfalso
    have hmem : (.inr (.inl b) : GNode3 T w h) ∈ l := List.mem_of_getElem? hz
    rcases hbd b hmem with hb | hb
    · rw [List.head?_eq_getElem?, ← hb] at hhd
      have := nodup_idx hnd hz hhd
      omega
    · rw [List.getLast?_eq_getElem?, ← hb] at hlast
      have := nodup_idx hnd hz hlast
      omega
  · exact absurd rfl (hzf F)

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- **(R) on a T2 path**: for two family nodes of a T2 path with no family node between them, the check after the
first and the check before the second lie in blocks more than `a1` apart. -/
theorem path_R3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {l : List (GNode3 T w h)} {x y : GNode3 T w h}
    (hhd : l.head? = some x) (hlast : l.getLast? = some y) (hnd : l.Nodup) (hch : List.IsChain (S.gadj3 Z ny E) l)
    (hbd : ∀ b : Bool, (.inr (.inl b) : GNode3 T w h) ∈ l →
      (.inr (.inl b) : GNode3 T w h) = x ∨ (.inr (.inl b) : GNode3 T w h) = y)
    {i j : ℕ} {Fm Fm' : Finset V3} (hij : i < j) (hi : l[i]? = some (.inr (.inr Fm)))
    (hj : l[j]? = some (.inr (.inr Fm'))) (hmid : ∀ k, i < k → k < j → ∀ F, l[k]? ≠ some (.inr (.inr F))) :
    ∃ u v : PVert3 T w h, l[i + 1]? = some (.inl u) ∧ l[j - 1]? = some (.inl v) ∧
      Const.a1 < dist3 (blockOf3 u) (blockOf3 v) := by
  obtain ⟨hjl, _⟩ := List.getElem?_eq_some_iff.1 hj
  have hi1 : i + 1 < j := by
    by_contra hc
    have hj' : j = i + 1 := by omega
    rw [hj'] at hj
    exact S.not_gadj_fam_fam3 Z (chain_step hch hi hj)
  obtain ⟨z1, hz1⟩ : ∃ z, l[i + 1]? = some z := ⟨l[i + 1], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨z2, hz2⟩ : ∃ z, l[j - 1]? = some z := ⟨l[j - 1], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨u, rfl⟩ := inner_check3 hhd hlast hnd hbd (by omega) (by omega) hz1
    (fun F hF => hmid (i + 1) (by omega) (by omega) F (hF ▸ hz1))
  obtain ⟨v, rfl⟩ := inner_check3 hhd hlast hnd hbd (by omega) (by omega) hz2
    (fun F hF => hmid (j - 1) (by omega) (by omega) F (hF ▸ hz2))
  refine ⟨u, v, hz1, hz2, ?_⟩
  obtain ⟨hFm, hu, hou⟩ := S.gadj_fam_check3 Z (chain_step hch hi hz1)
  have hz2' : l[j - 1 + 1]? = some (.inr (.inr Fm')) := by rw [show j - 1 + 1 = j by omega]; exact hj
  obtain ⟨hFm', hv, hov⟩ := S.gadj_check_fam3 Z (chain_step hch hz2 hz2')
  refine S.om_far3 (ny := ny) hou hov ?_
  rw [famF_eq_of_mem_families3 hFm hu, famF_eq_of_mem_families3 hFm' hv]
  intro hFF
  rw [hFF] at hi
  have := nodup_idx hnd hi hj
  omega

end Stage13

end QECD1
