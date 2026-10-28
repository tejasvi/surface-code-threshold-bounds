import QECCountComp.Core

/-!
# Kernel-friendly certificate checks

The same checks as in `Core.lean`, written for evaluation by the kernel (`decide +kernel`): no arrays, no strings.

* The listed states form a binary search tree `KTree` of (key, `H`, mask). The mask marks the candidate steps whose
  window of `K + 1` edges the generator excluded; it is only a hint: every claimed exclusion is re-found and checked
  (`exclWinK`), and an unexcluded candidate with a listed target simply enters the row.
* The witness search `findWK` is `findW` with the matching found by recursion over the points instead of dynamic
  programming over subsets (untrusted; its output is checked by `checkW`).
-/

namespace QECComp

/-- Listed states: a binary tree of (key, potential, mask). -/
inductive KTree where
  | leaf : KTree
  | node : KTree → Nat → Nat → Nat → KTree → KTree

namespace KTree

/-- The potential and mask of the key `x`, if listed (search in a binary search tree). -/
def find : KTree → Nat → Option (Nat × Nat)
  | leaf, _ => none
  | node l k h m r, x => if Nat.blt x k then l.find x else if Nat.blt k x then r.find x else some (h, m)

/-- The entries in order. -/
def toList : KTree → List (Nat × Nat × Nat)
  | leaf => []
  | node l k h m r => l.toList ++ (k, h, m) :: r.toList

end KTree

/-- The points of odd degree in the C-edges of a walk with points `pts` and labels `labs` (as a list). -/
def oddVertsL (pts : List (List Int)) (labs : List Bool) : List (List Int) :=
  let m := labs.length
  ((List.range (m + 1)).filter (fun k =>
    ((if k > 0 && labs.getD (k - 1) false then 1 else 0) + (if k < m && labs.getD k false then 1 else 0)) % 2 == 1)
  ).map (fun k => pts.getD k [])

/-- Least-cost, then least-`Φ`, perfect matching by recursion: the first point is paired with each other point. -/
def matchRec (n : Nat) (c : List Int) : Nat → List (List Int) → Option (Nat × Int × List (List Int × List Int))
  | 0, _ => none
  | _, [] => some (0, 0, [])
  | fuel + 1, a :: rest =>
    rest.foldl (fun best b =>
      match matchRec n c fuel (rest.erase b) with
      | none => best
      | some (cc, ff, ps) =>
        let cost := cc + l1 a b
        let phi := ff + phiE c (altEdges n (chainAlt n a (geoDirs n c a b)))
        match best with
        | none => some (cost, phi, (a, b) :: ps)
        | some (bc, bf, _) => if cost < bc || (cost == bc && decide (phi < bf)) then some (cost, phi, (a, b) :: ps)
            else best) none

/-- The witness search of `findW`, with `matchRec`. -/
def findWK (n : Nat) (c : List Int) (w : List (Nat × Bool)) : Option Wit :=
  let pts := walkPts n (zeros n) (w.map Prod.fst)
  let X := cEdges n w
  let Y := eEdges n w
  let nC := X.length
  let nE := Y.length
  let a := zeros n
  let b := pts.getLastD a
  let dist := l1 a b
  let geo := chainAlt n a (geoDirs n c a b)
  let phC := phiE c X
  if nC > nE + dist then some ⟨true, geo⟩
  else if nC > 0 && nC == nE + dist && decide (phiE c Y + phiE c (altEdges n geo) < phC) then some ⟨true, geo⟩
  else if nC < 2 then none
  else
    let T := oddVertsL pts (w.map Prod.snd)
    match matchRec n c (T.length + 1) T with
    | none => none
    | some (cost, f, pairs) =>
      if nC > cost || (nC == cost && decide (f < phC)) then
        let alt := pairs.flatMap (fun pr => chainAlt n pr.1 (geoDirs n c pr.1 pr.2))
        some ⟨false, if nC > cost || nodupE (altEdges n alt) then alt else oddAlt n alt⟩
      else none

/-- The window `u` is excluded by a witness found by `findWK` and checked. -/
def exclWinK (P : Params) (u : List (Nat × Bool)) : Bool :=
  match findWK P.n P.c u with
  | some W => checkW P.n P.c u W
  | none => false

/-- Some window of `2..K+1` edges ending with the last edge of `u` is excluded (found by `findWK` and checked). -/
def exclEndingK (P : Params) (u : List (Nat × Bool)) : Bool :=
  (List.range (P.K + 2)).any (fun m => decide (2 ≤ m) && decide (m ≤ u.length) && exclWinK P (u.drop (u.length - m)))

/-- The weighted sum over the successors of the state `s` with mask `mask` (`none` if a candidate is neither
excluded nor listed, or a claimed exclusion fails). -/
def rowSumK (P : Params) (t : KTree) (mask : Nat) (s : List (Nat × Bool)) : Option Nat :=
  ((candList P.n).zip (List.range (4 * P.n))).foldl (fun acc xi =>
    match acc with
    | none => none
    | some tot =>
      let u := s ++ [xi.1]
      if !selfAvoid P.n u then some tot
      else match t.find (keyOf P.n u.tail) with
        | some hm =>
          if mask / 2 ^ xi.2 % 2 == 1 then (if exclWinK P u then some tot else none)
          else some (tot + (if xi.1.2 then P.wC else P.wE) * hm.1)
        | none => if exclEndingK P u then some tot else none) (some 0)

/-- The row of the entry `(k, h, mask)`. -/
def rowCheckK (P : Params) (t : KTree) (e : Nat × Nat × Nat) : Bool :=
  decide (0 < P.Hmin) && decide (P.Hmin ≤ e.2.1) &&
  match rowSumK P t e.2.2 (decodeKey P.n P.K e.1) with
  | some tot => decide (tot * P.lamD ≤ P.lamN * P.Q * e.2.1)
  | none => false

/-- The rows of the entries `lo, …, hi - 1` (in order). -/
def rowsOKK (P : Params) (t : KTree) (lo hi : Nat) : Bool :=
  ((t.toList.drop lo).take (hi - lo)).all (rowCheckK P t)

/-- Start completeness (as `dfsOK`). -/
def dfsOKK (P : Params) (t : KTree) : Nat → List (Nat × Bool) → Bool
  | 0, pfx => (t.find (keyOf P.n pfx)).isSome
  | r + 1, pfx => (candList P.n).all (fun x =>
      let u := pfx ++ [x]
      !selfAvoid P.n u || exclEndingK P u || dfsOKK P t r u)

/-- The part of the start check that begins with the `j`-th candidate step. -/
def dfsTopK (P : Params) (t : KTree) (j : Nat) : Bool :=
  match (candList P.n)[j]? with
  | some x => !selfAvoid P.n [x] || exclEndingK P [x] || dfsOKK P t (P.K - 1) [x]
  | none => true

/-- The part of the start check that begins with the `j1`-th and then the `j2`-th candidate steps. -/
def dfsTop2K (P : Params) (t : KTree) (j1 j2 : Nat) : Bool :=
  match (candList P.n)[j1]?, (candList P.n)[j2]? with
  | some x1, some x2 => !selfAvoid P.n [x1] || exclEndingK P [x1] || !selfAvoid P.n [x1, x2] ||
      exclEndingK P [x1, x2] || dfsOKK P t (P.K - 2) [x1, x2]
  | _, _ => true

/-- The start-sum bound over the listed states (as `startOK`). -/
def startOKK (P : Params) (t : KTree) : Bool :=
  let tot := t.toList.foldl (fun (acc : List Nat) e =>
    let c := nCOf P.n P.K e.1
    acc.set c (acc.getD c 0 + e.2.1)) (List.replicate (P.K + 1) 0)
  let S := (List.range (P.K + 1)).foldl (fun acc c => acc + tot.getD c 0 * P.wE ^ (P.K - c) * P.wC ^ c) 0
  decide ((P.wE + P.wC) ^ 2 * S * P.K0d ≤ P.K0n * P.Hmin * P.Q ^ (P.K + 2))

end QECComp
