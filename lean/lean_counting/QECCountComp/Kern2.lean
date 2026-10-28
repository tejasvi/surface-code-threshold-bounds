import QECCountComp.Kern

/-!
# Kernel route, version 2: checks per subtree

For certificates with millions of states the checks of `Kern.lean` that walk `t.toList` of the whole tree (`rowsOKK`,
`startOKK`) are too costly in the kernel. Here every check walks one named subtree only, and the facts are combined
structurally over the (named) internal nodes:

* `KTree.allE f t`: `f` holds at every entry of `t` (rows: `allE (rowCheckK P tFull) tSub`, lookups in the full tree);
* `totK P t`: the totals of `H` by the number of C-labels over the entries of `t` (start sums), combined with `addL`;
* `startOK2 P tot`: the start-sum bound from the totals;
* `dfsPreK P t js []`: the start check restricted to the walks whose first steps are the candidates of indices `js`.
-/

namespace QECComp

namespace KTree

/-- `f` holds at every entry of the tree. -/
def allE (f : Nat × Nat × Nat → Bool) : KTree → Bool
  | leaf => true
  | node l k h m r => (allE f l && f (k, h, m)) && allE f r

end KTree

/-- Pointwise sum of two lists of naturals (the tail of the longer list kept). -/
def addL : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addL xs ys

/-- The totals of `H` by the number of C-labels, over the entries of a tree (`K + 1` entries). -/
def totK (P : Params) : KTree → List Nat
  | .leaf => List.replicate (P.K + 1) 0
  | .node l k h _ r =>
    addL (totK P l) (addL ((List.replicate (P.K + 1) 0).set (nCOf P.n P.K k) h) (totK P r))

/-- The start-sum bound from the totals (as `startOKK`). -/
def startOK2 (P : Params) (tot : List Nat) : Bool :=
  let S := (List.range (P.K + 1)).foldl (fun acc c => acc + tot.getD c 0 * P.wE ^ (P.K - c) * P.wC ^ c) 0
  decide ((P.wE + P.wC) ^ 2 * S * P.K0d ≤ P.K0n * P.Hmin * P.Q ^ (P.K + 2))

/-- The start check for the walks that continue the prefix `pfx` with the candidate steps of indices `js`, then with
any `K - |pfx| - |js|` further steps (as `dfsOKK`). -/
def dfsPreK (P : Params) (t : KTree) : List Nat → List (Nat × Bool) → Bool
  | [], pfx => dfsOKK P t (P.K - pfx.length) pfx
  | j :: js, pfx =>
    match (candList P.n)[j]? with
    | some x =>
      let u := pfx ++ [x]
      !selfAvoid P.n u || exclEndingK P u || dfsPreK P t js u
    | none => true

end QECComp
