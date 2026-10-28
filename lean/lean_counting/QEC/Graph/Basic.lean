import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.List
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Decoding graphs: vertices, edge sets, boundaries, vertex lists

A decoding graph has the detectors `det v` (`v : V`) and two boundary vertices `b1`, `b2` (§1.3).
Edges are elements of `Sym2 (Vx V)`; a set of edges is a `Finset`. The boundary `bd C` of a set of edges is
the set of detectors of odd degree in `C`. Paths are vertex lists.
-/

namespace QEC

open Finset
open scoped symmDiff

/-- Vertices of a decoding graph: the detectors and the boundary vertices `b1`, `b2`. -/
inductive Vx (V : Type*) where
  | det (v : V) : Vx V
  | b1 : Vx V
  | b2 : Vx V
  deriving DecidableEq, Fintype

namespace Vx

variable {V : Type*}

/-- The detector vertices. -/
def IsDet : Vx V → Prop
  | det _ => True
  | _ => False

@[simp] theorem isDet_det (v : V) : IsDet (det v) := trivial
@[simp] theorem not_isDet_b1 : ¬ IsDet (b1 : Vx V) := id
@[simp] theorem not_isDet_b2 : ¬ IsDet (b2 : Vx V) := id

theorem isDet_iff (x : Vx V) : IsDet x ↔ x ≠ b1 ∧ x ≠ b2 := by
  cases x <;> simp [IsDet]

end Vx

section Graph

variable {X : Type*} [DecidableEq X]

/-- The simple graph with edge set `Eg` (diagonal elements of `Eg` are ignored). -/
def decGraph (Eg : Finset (Sym2 X)) : SimpleGraph X where
  Adj x y := x ≠ y ∧ s(x, y) ∈ Eg
  symm := ⟨fun _ _ h => ⟨h.1.symm, Sym2.eq_swap ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (Eg : Finset (Sym2 X)) : DecidableRel (decGraph Eg).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ s(x, y) ∈ Eg))

theorem decGraph_adj {Eg : Finset (Sym2 X)} {x y : X} :
    (decGraph Eg).Adj x y ↔ x ≠ y ∧ s(x, y) ∈ Eg := Iff.rfl

theorem decGraph_mono {R Eg : Finset (Sym2 X)} (h : R ⊆ Eg) {x y : X} (hxy : (decGraph R).Adj x y) :
    (decGraph Eg).Adj x y := ⟨hxy.1, h hxy.2⟩

/-- The number of edges of `C` at `x`. -/
def vdeg (C : Finset (Sym2 X)) (x : X) : ℕ := #(C.filter (fun e => x ∈ e))

theorem card_symmDiff_add {α : Type*} [DecidableEq α] (s t : Finset α) :
    #(s ∆ t) + 2 * #(s ∩ t) = #s + #t := by
  have h1 := card_sdiff_add_card_inter s t
  have h2 := card_sdiff_add_card_inter t s
  have hd : Disjoint (s \ t) (t \ s) := disjoint_sdiff_sdiff
  rw [Finset.symmDiff_def, card_union_of_disjoint hd, inter_comm t s] at *
  omega

theorem vdeg_symmDiff (C D : Finset (Sym2 X)) (x : X) :
    vdeg (C ∆ D) x + 2 * vdeg (C ∩ D) x = vdeg C x + vdeg D x := by
  unfold vdeg
  have h1 : (C ∆ D).filter (fun e => x ∈ e) = C.filter (fun e => x ∈ e) ∆ D.filter (fun e => x ∈ e) := by
    ext e; simp only [mem_filter, mem_symmDiff]; tauto
  have h2 : (C ∩ D).filter (fun e => x ∈ e) = C.filter (fun e => x ∈ e) ∩ D.filter (fun e => x ∈ e) := by
    ext e; simp only [mem_filter, mem_inter]; tauto
  rw [h1, h2]
  exact card_symmDiff_add _ _

theorem odd_vdeg_symmDiff (C D : Finset (Sym2 X)) (x : X) :
    Odd (vdeg (C ∆ D) x) ↔ ¬ (Odd (vdeg C x) ↔ Odd (vdeg D x)) := by
  have h := vdeg_symmDiff C D x
  constructor
  · intro hodd
    rcases Nat.even_or_odd (vdeg C x) with hC | hC <;> rcases Nat.even_or_odd (vdeg D x) with hD | hD
    · exfalso; obtain ⟨k, hk⟩ := hodd; obtain ⟨a, ha⟩ := hC; obtain ⟨b, hb⟩ := hD; omega
    · simp only [Nat.not_odd_iff_even.mpr hC, hD, iff_true, not_false_eq_true]
    · simp only [hC, Nat.not_odd_iff_even.mpr hD, iff_false, not_true_eq_false, not_false_eq_true]
    · exfalso; obtain ⟨k, hk⟩ := hodd; obtain ⟨a, ha⟩ := hC; obtain ⟨b, hb⟩ := hD; omega
  · intro hne
    rcases Nat.even_or_odd (vdeg C x) with hC | hC <;> rcases Nat.even_or_odd (vdeg D x) with hD | hD
    · exact absurd ⟨fun h' => absurd h' (Nat.not_odd_iff_even.mpr hC),
        fun h' => absurd h' (Nat.not_odd_iff_even.mpr hD)⟩ hne
    · obtain ⟨a, ha⟩ := hC; obtain ⟨b, hb⟩ := hD; exact ⟨a + b - vdeg (C ∩ D) x, by omega⟩
    · obtain ⟨a, ha⟩ := hC; obtain ⟨b, hb⟩ := hD; exact ⟨a + b - vdeg (C ∩ D) x, by omega⟩
    · exact absurd ⟨fun _ => hD, fun _ => hC⟩ hne

end Graph

section Boundary

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The boundary `∂C ⊆ V`: detectors of odd degree in `C`. -/
def bd (C : Finset (Sym2 (Vx V))) : Finset V := univ.filter (fun v => Odd (vdeg C (Vx.det v)))

theorem mem_bd {C : Finset (Sym2 (Vx V))} {v : V} : v ∈ bd C ↔ Odd (vdeg C (Vx.det v)) := by
  simp [bd]

theorem bd_symmDiff (C D : Finset (Sym2 (Vx V))) : bd (C ∆ D) = bd C ∆ bd D := by
  ext v
  simp only [mem_bd, mem_symmDiff, odd_vdeg_symmDiff]
  tauto

end Boundary

section Lists

variable {X : Type*}

/-- The edges `s(x_i, x_{i+1})` of a vertex list. -/
def ledges : List X → List (Sym2 X)
  | x :: y :: l => s(x, y) :: ledges (y :: l)
  | _ => []

/-- The product of `a` over the consecutive pairs of a vertex list. -/
def lwt (a : Sym2 X → ℝ) : List X → ℝ
  | x :: y :: l => a s(x, y) * lwt a (y :: l)
  | _ => 1

@[simp] theorem ledges_nil : ledges ([] : List X) = [] := rfl
@[simp] theorem ledges_single (x : X) : ledges [x] = [] := rfl
@[simp] theorem ledges_cons_cons (x y : X) (l : List X) :
    ledges (x :: y :: l) = s(x, y) :: ledges (y :: l) := rfl
@[simp] theorem lwt_nil (a : Sym2 X → ℝ) : lwt a [] = 1 := rfl
@[simp] theorem lwt_single (a : Sym2 X → ℝ) (x : X) : lwt a [x] = 1 := rfl
@[simp] theorem lwt_cons_cons (a : Sym2 X → ℝ) (x y : X) (l : List X) :
    lwt a (x :: y :: l) = a s(x, y) * lwt a (y :: l) := rfl

theorem lwt_eq_prod (a : Sym2 X → ℝ) : ∀ l : List X, lwt a l = ((ledges l).map a).prod
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by simp [lwt_eq_prod a (y :: l)]

theorem lwt_nonneg {a : Sym2 X → ℝ} (ha : ∀ e, 0 ≤ a e) : ∀ l : List X, 0 ≤ lwt a l
  | [] => zero_le_one
  | [_] => zero_le_one
  | x :: y :: l => mul_nonneg (ha _) (lwt_nonneg ha (y :: l))

theorem mem_of_mem_ledges {e : Sym2 X} {z : X} : ∀ {l : List X}, e ∈ ledges l → z ∈ e → z ∈ l
  | [], h, _ => by simp at h
  | [_], h, _ => by simp at h
  | x :: y :: l, h, hz => by
    simp only [ledges_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · rcases Sym2.mem_iff.mp hz with rfl | rfl <;> simp
    · exact List.mem_cons_of_mem _ (mem_of_mem_ledges h hz)

theorem ledges_nodup : ∀ {l : List X}, l.Nodup → (ledges l).Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_nil
  | x :: y :: l, h => by
    rw [ledges_cons_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ledges_nodup (List.nodup_cons.mp h).2⟩
    have := mem_of_mem_ledges hm (Sym2.mem_mk_left x y)
    exact (List.nodup_cons.mp h).1 this

variable [DecidableEq X]

theorem ledges_subset_of_chain {R : Finset (Sym2 X)} :
    ∀ {l : List X}, l.IsChain (decGraph R).Adj → ∀ e ∈ ledges l, e ∈ R
  | [], _, e, h => by simp at h
  | [_], _, e, h => by simp at h
  | x :: y :: l, hc, e, h => by
    rw [List.isChain_cons_cons] at hc
    simp only [ledges_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact hc.1.2
    · exact ledges_subset_of_chain hc.2 e h

/-- Parity of the degree in the edges of a vertex list without repetitions: the degree of `z`, plus one
for each end equal to `z`, is even. -/
theorem even_countP_ledges (z : X) :
    ∀ {l : List X}, l.Nodup → l ≠ [] →
      Even ((ledges l).countP (fun e => z ∈ e) + (if l.head? = some z then 1 else 0) +
        (if l.getLast? = some z then 1 else 0))
  | [], _, h => absurd rfl h
  | [x], _, _ => by
    simp only [ledges_single, List.countP_nil, List.head?_cons, List.getLast?_singleton, zero_add]
    split_ifs <;> simp
  | x :: y :: l, hnd, _ => by
    have hxy : x ≠ y := fun h => (List.nodup_cons.mp hnd).1 (h ▸ List.mem_cons_self)
    have ih := even_countP_ledges z (l := y :: l) (List.nodup_cons.mp hnd).2 (List.cons_ne_nil _ _)
    have hlast : (x :: y :: l).getLast? = (y :: l).getLast? := by simp [List.getLast?_cons_cons]
    rw [hlast, ledges_cons_cons, List.countP_cons]
    simp only [List.head?_cons, Option.some.injEq] at ih ⊢
    have key : (if decide (z ∈ s(x, y)) = true then 1 else 0) =
        (if x = z then 1 else 0) + (if y = z then 1 else 0) := by
      by_cases h1 : x = z
      · subst h1
        have : y ≠ x := fun h => hxy h.symm
        simp [this]
      · by_cases h2 : y = z
        · subst h2
          simp [h1]
        · have : ¬ z ∈ s(x, y) := by
            rw [Sym2.mem_iff]
            rintro (h | h)
            · exact h1 h.symm
            · exact h2 h.symm
          simp [this, h1, h2]
    rw [key]
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + (if x = z then 1 else 0), by omega⟩

/-- The edge set of a vertex list. -/
def pedges (l : List X) : Finset (Sym2 X) := (ledges l).toFinset

theorem vdeg_pedges {l : List X} (hl : l.Nodup) (z : X) :
    vdeg (pedges l) z = (ledges l).countP (fun e => z ∈ e) := by
  unfold vdeg pedges
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((ledges_nodup hl).filter _)]
  congr 1
  ext e
  simp

theorem prod_pedges (a : Sym2 X → ℝ) {l : List X} (hl : l.Nodup) :
    ∏ e ∈ pedges l, a e = lwt a l := by
  rw [pedges, List.prod_toFinset _ (ledges_nodup hl), lwt_eq_prod]

/-- `l` is a simple path from `u` to `v` in `G`. -/
structure IsSPath (G : SimpleGraph X) (u v : X) (l : List X) : Prop where
  head : l.head? = some u
  last : l.getLast? = some v
  chain : l.IsChain G.Adj
  nodup : l.Nodup

end Lists

section PathBoundary

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of a simple path from `b1` to `b2` have empty boundary. -/
theorem bd_pedges_path {G : SimpleGraph (Vx V)} {l : List (Vx V)} (hp : IsSPath G .b1 .b2 l) :
    bd (pedges l) = ∅ := by
  ext v
  simp only [mem_bd, Finset.notMem_empty, iff_false, Nat.not_odd_iff_even]
  have hne : l ≠ [] := by
    rintro rfl
    exact absurd hp.head (by simp)
  have h := even_countP_ledges (Vx.det v) hp.nodup hne
  rw [hp.head, hp.last] at h
  simp only [Option.some.injEq, reduceCtorEq, if_false, add_zero] at h
  rwa [vdeg_pedges hp.nodup]

end PathBoundary

end QEC
