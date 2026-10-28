import QECCountComp.KernT

/-!
# Packed trees of listed states (kernel route, large certificates)

`PTree` is `KTree` with packed leaves: `pl n x` holds `n` records in the natural number `x`, record `i` in the bits
`W i, …, W i + W - 1` (`W = kb + hb + mb`), each record `key · 2^(hb+mb) + potential · 2^mb + mask`, keys ascending;
internal nodes hold one entry each, as in `KTree`. One literal per leaf keeps the data small; the kernel decodes a
record with its built-in shifts and remainders. `find` searches the internal nodes and then the leaf by bisection;
it returns only records of the tree (`find_memP`), which is all the soundness proofs use.
-/

namespace QECComp

/-- Record widths of a packed tree: key, potential and mask bits. -/
structure PW where
  kb : Nat
  hb : Nat
  mb : Nat

namespace PW

/-- The width of a record. -/
def w (p : PW) : Nat := p.kb + p.hb + p.mb

/-- Record `i` of the packed leaf `x`. -/
def recAt (p : PW) (x i : Nat) : Nat := (x >>> (p.w * i)) % 2 ^ p.w

/-- The key of a record. -/
def key (p : PW) (r : Nat) : Nat := r >>> (p.hb + p.mb)

/-- The potential of a record. -/
def pot (p : PW) (r : Nat) : Nat := (r >>> p.mb) % 2 ^ p.hb

/-- The mask of a record. -/
def msk (p : PW) (r : Nat) : Nat := r % 2 ^ p.mb

/-- The entry (key, potential, mask) of record `i` of the leaf `x`. -/
def ent (p : PW) (x i : Nat) : Nat × Nat × Nat :=
  let r := p.recAt x i
  (p.key r, p.pot r, p.msk r)

end PW

/-- Listed states: internal nodes with one entry each, leaves packed. -/
inductive PTree where
  | pl : Nat → Nat → PTree
  | node : PTree → Nat → Nat → Nat → PTree → PTree

/-- Bisection for the key `k` among the records `lo, …, hi - 1` of the leaf `x` (fuel). -/
def bsP (p : PW) (x k : Nat) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if hi ≤ lo then none else
    let mid := (lo + hi) / 2
    let e := p.ent x mid
    if k < e.1 then bsP p x k fuel lo mid
    else if e.1 < k then bsP p x k fuel (mid + 1) hi
    else some e.2

namespace PTree

/-- The potential and mask of the key `k`, if listed. -/
def find (p : PW) : PTree → Nat → Option (Nat × Nat)
  | pl n x, k => bsP p x k (n + 1) 0 n
  | node l k0 h m r, k => if k < k0 then l.find p k else if k0 < k then r.find p k else some (h, m)

/-- The entries in order. -/
def toList (p : PW) : PTree → List (Nat × Nat × Nat)
  | pl n x => (List.range n).map (p.ent x)
  | node l k h m r => l.toList p ++ (k, h, m) :: r.toList p

/-- `f` holds at every entry of the tree. -/
def allE (p : PW) (f : Nat × Nat × Nat → Bool) : PTree → Bool
  | pl n x => (List.range n).all (fun i => f (p.ent x i))
  | node l k h m r => (allE p f l && f (k, h, m)) && allE p f r

/-- The sums of the contributions `f` of the entries (pointwise, with `addL`). -/
def tot (p : PW) (f : Nat × Nat × Nat → List Nat) : PTree → List Nat
  | pl n x => sumL ((List.range n).map (fun i => f (p.ent x i)))
  | node l k h m r => addL (tot p f l) (addL (f (k, h, m)) (tot p f r))

end PTree

end QECComp

namespace QECComp

namespace PTree

/-- `f` holds at the records `lo, …, hi - 1` of a packed leaf (true for an internal node). -/
def allEr (p : PW) (f : Nat × Nat × Nat → Bool) : PTree → Nat → Nat → Bool
  | pl _ x, lo, hi => (List.range' lo (hi - lo)).all (fun i => f (p.ent x i))
  | node .., _, _ => true

/-- The tree is a leaf with `m` records. -/
def isLeafN : PTree → Nat → Bool
  | pl n _, m => n == m
  | node .., _ => false

end PTree

end QECComp

namespace QECComp

theorem PTree.allEr_append {p : PW} {f : Nat × Nat × Nat → Bool} {t : PTree} {a b c : Nat} (hab : a ≤ b)
    (hbc : b ≤ c) (h1 : PTree.allEr p f t a b = true) (h2 : PTree.allEr p f t b c = true) :
    PTree.allEr p f t a c = true := by
  cases t with
  | pl n x =>
    simp only [PTree.allEr, List.all_eq_true, List.mem_range'_1] at h1 h2 ⊢
    intro i hi
    by_cases hib : i < b
    · exact h1 i ⟨hi.1, by omega⟩
    · exact h2 i ⟨by omega, by omega⟩
  | node l k h m r => rfl

theorem PTree.allE_of_allEr {p : PW} {f : Nat × Nat × Nat → Bool} {t : PTree} {n : Nat} (hl : t.isLeafN n = true)
    (h : PTree.allEr p f t 0 n = true) : PTree.allE p f t = true := by
  cases t with
  | pl m x =>
    simp only [PTree.isLeafN, beq_iff_eq] at hl
    subst hl
    simp only [PTree.allEr, PTree.allE, List.all_eq_true, List.mem_range'_1, List.mem_range] at h ⊢
    intro i hi
    exact h i ⟨Nat.zero_le _, by omega⟩
  | node l k h0 m r => simp [PTree.isLeafN] at hl

end QECComp
