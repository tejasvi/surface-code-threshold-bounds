import QECCountComp.KernP
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.SplitIfs

/-!
# Packed trees of listed states: the lemmas used by the kernel route

For `PTree` (`QECCountComp/KernP.lean`): the lookup returns only entries of the tree (`find_memP`), the per-entry
checks (`allE_iffP`, `allE_nodeP`), and the sums of the contributions (`totP_eq`). The facts about `addL` and `sumL`
carry a `P` suffix.
-/

namespace QEC

open QECComp

theorem addL_nilP : ∀ xs : List ℕ, addL xs [] = xs
  | [] => rfl
  | _ :: _ => rfl

theorem addL_assocP : ∀ xs ys zs : List ℕ, addL (addL xs ys) zs = addL xs (addL ys zs)
  | [], _, _ => rfl
  | x :: xs, [], zs => by
    show addL (x :: xs) zs = addL (x :: xs) (addL [] zs)
    rfl
  | x :: xs, y :: ys, [] => by
    rw [addL_nilP, addL_nilP]
  | x :: xs, y :: ys, z :: zs => by
    show (x + y + z) :: addL (addL xs ys) zs = (x + (y + z)) :: addL xs (addL ys zs)
    rw [addL_assocP xs ys zs, Nat.add_assoc]

theorem sumL_appendP : ∀ (a b : List (List ℕ)), sumL (a ++ b) = addL (sumL a) (sumL b)
  | [], _ => rfl
  | x :: xs, b => by
    show addL x (sumL (xs ++ b)) = addL (addL x (sumL xs)) (sumL b)
    rw [sumL_appendP xs b, addL_assocP]

/-- The bisection returns only records of the leaf, between `lo` and `hi`, with the key searched for. -/
theorem bsP_mem {p : PW} {x k : ℕ} : ∀ (fuel lo hi : ℕ) {e : ℕ × ℕ}, bsP p x k fuel lo hi = some e →
    ∃ i, lo ≤ i ∧ i < hi ∧ p.ent x i = (k, e.1, e.2)
  | 0, _, _, _, h => by simp [bsP] at h
  | fuel + 1, lo, hi, e, h => by
    simp only [bsP] at h
    split_ifs at h with h1 h2 h3
    · obtain ⟨i, hi1, hi2, he⟩ := bsP_mem fuel lo ((lo + hi) / 2) h
      exact ⟨i, hi1, by omega, he⟩
    · obtain ⟨i, hi1, hi2, he⟩ := bsP_mem fuel ((lo + hi) / 2 + 1) hi h
      exact ⟨i, by omega, hi2, he⟩
    · refine ⟨(lo + hi) / 2, by omega, by omega, ?_⟩
      have hk : (p.ent x ((lo + hi) / 2)).1 = k := by omega
      have he : (p.ent x ((lo + hi) / 2)).2 = e := Option.some.inj h
      rw [← hk, ← he]

/-- **The lookup of a packed tree returns only entries of the tree.** -/
theorem find_memP {p : PW} {t : PTree} {k h m : ℕ} (hf : t.find p k = some (h, m)) : (k, h, m) ∈ t.toList p := by
  induction t with
  | pl n x =>
    simp only [PTree.find] at hf
    obtain ⟨i, -, hi, he⟩ := bsP_mem (n + 1) 0 n hf
    simp only [PTree.toList, List.mem_map, List.mem_range]
    exact ⟨i, hi, he⟩
  | node l k0 h0 m0 r ihl ihr =>
    simp only [PTree.find] at hf
    simp only [PTree.toList, List.mem_append, List.mem_cons]
    split_ifs at hf with h1 h2
    · exact Or.inl (ihl hf)
    · exact Or.inr (Or.inr (ihr hf))
    · have hk : k = k0 := by omega
      have hm : (h0, m0) = (h, m) := Option.some.inj hf
      simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact Or.inr (Or.inl (by rw [hk]))

/-- **The per-entry checks of a packed tree.** -/
theorem allE_iffP {p : PW} {f : ℕ × ℕ × ℕ → Bool} {t : PTree} :
    PTree.allE p f t = true ↔ ∀ e ∈ t.toList p, f e = true := by
  induction t with
  | pl n x =>
    simp only [PTree.allE, PTree.toList, List.all_eq_true, List.mem_range, List.mem_map]
    constructor
    · rintro h e ⟨i, hi, rfl⟩
      exact h i hi
    · intro h i hi
      exact h _ ⟨i, hi, rfl⟩
  | node l k h m r ihl ihr =>
    simp only [PTree.allE, PTree.toList, Bool.and_eq_true, List.mem_append, List.mem_cons, ihl, ihr]
    constructor
    · rintro ⟨⟨hl, hm⟩, hr⟩ e (he | rfl | he)
      · exact hl e he
      · exact hm
      · exact hr e he
    · intro H
      exact ⟨⟨fun e he => H e (Or.inl he), H _ (Or.inr (Or.inl rfl))⟩, fun e he => H e (Or.inr (Or.inr he))⟩

theorem allE_nodeP {p : PW} {f : ℕ × ℕ × ℕ → Bool} (l r : PTree) (k h m : ℕ) :
    PTree.allE p f (PTree.node l k h m r) = ((PTree.allE p f l && f (k, h, m)) && PTree.allE p f r) := rfl

/-- **The sums of the contributions over a packed tree.** -/
theorem totP_eq (p : PW) (f : ℕ × ℕ × ℕ → List ℕ) (t : PTree) : PTree.tot p f t = sumL ((t.toList p).map f) := by
  induction t with
  | pl n x =>
    simp only [PTree.tot, PTree.toList, List.map_map]
    rfl
  | node l k h m r ihl ihr =>
    simp only [PTree.tot, PTree.toList, List.map_append, List.map_cons]
    rw [sumL_appendP, ihl, ihr]
    rfl

end QEC

#print axioms QEC.find_memP
#print axioms QEC.allE_iffP
#print axioms QEC.allE_nodeP
#print axioms QEC.totP_eq
