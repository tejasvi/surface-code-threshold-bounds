/-!
# Computational core of the counting certificates

This module imports only Lean core; it is compiled to native code (`precompileModules`).

Points of `ℤⁿ` are lists of `n` integers. A direction is a number `d < 2n`: axis `d / 2`, sign `+` iff `d` is even
(for `n = 2`: `0, 1, 2, 3` = `+x, -x, +y, -y`; for `n = 3`: `+t, -t, +X, -X, +Y, -Y`). A labelled pattern is a list of
pairs (direction, label), the label `true` marking a C-edge and `false` an E-edge. Edges are ordered pairs of points.

Trusted (the proofs are about these functions): the geometry (`vecOf`, `addP`, `phiP`, `walkPts`, `edgesFrom`,
`degC`, `inBB`, `phiE`, `nodupE`), the witness check `checkW`, the keys and the certificate checks of the last
section. Untrusted (only their outputs are checked): the witness search `findW` and its helpers.
-/

namespace QECComp

/-! ## Points, directions, walks -/

/-- The origin of `ℤⁿ`. -/
def zeros (n : Nat) : List Int := List.replicate n 0

/-- The unit vector of direction `d`. -/
def vecOf (n d : Nat) : List Int :=
  (List.range n).map (fun i => if i = d / 2 then (if d % 2 = 0 then (1 : Int) else -1) else 0)

/-- Coordinatewise sum. -/
def addP : List Int → List Int → List Int
  | a :: as, b :: bs => (a + b) :: addP as bs
  | _, _ => []

/-- `φ(x) = ∑ c_i x_i`. -/
def phiP : List Int → List Int → Int
  | c :: cs, x :: xs => c * x + phiP cs xs
  | _, _ => 0

/-- The points of the walk from `o` along the directions `ds`. -/
def walkPts (n : Nat) (o : List Int) : List Nat → List (List Int)
  | [] => [o]
  | d :: ds => o :: walkPts n (addP o (vecOf n d)) ds

/-- An edge: an ordered pair of points. -/
abbrev Edge := List Int × List Int

/-- The labelled edges of the walk from `o` along a labelled pattern. -/
def edgesFrom (n : Nat) (o : List Int) : List (Nat × Bool) → List (Edge × Bool)
  | [] => []
  | (d, l) :: w => ((o, addP o (vecOf n d)), l) :: edgesFrom n (addP o (vecOf n d)) w

/-- The C-edges (label `true`) of a pattern, from the origin. -/
def cEdges (n : Nat) (w : List (Nat × Bool)) : List Edge :=
  ((edgesFrom n (zeros n) w).filter (fun e => e.2)).map Prod.fst

/-- The E-edges (label `false`) of a pattern, from the origin. -/
def eEdges (n : Nat) (w : List (Nat × Bool)) : List Edge :=
  ((edgesFrom n (zeros n) w).filter (fun e => !e.2)).map Prod.fst

/-- The number of edges of `L` with an end at `x` (with multiplicity). -/
def degC (L : List Edge) (x : List Int) : Nat := L.countP (fun e => e.1 == x || e.2 == x)

/-- `A` and `B` have the same degree parity at every end of an edge of `A` or `B` (hence at every point). -/
def parOK (A B : List Edge) : Bool :=
  (A ++ B).all (fun e => degC A e.1 % 2 == degC B e.1 % 2 && degC A e.2 % 2 == degC B e.2 % 2)

/-- `x` has `n` coordinates and lies in the bounding box of `pts`. -/
def inBB (n : Nat) (pts : List (List Int)) (x : List Int) : Bool :=
  x.length == n && (List.range n).all (fun i =>
    pts.any (fun p => decide (p.getD i 0 ≤ x.getD i 0)) && pts.any (fun p => decide (x.getD i 0 ≤ p.getD i 0)))

/-- `Φ` of an edge list: the sum of `φ(a) + φ(b)` over its edges `(a, b)`. -/
def phiE (c : List Int) : List Edge → Int
  | [] => 0
  | e :: L => phiP c e.1 + phiP c e.2 + phiE c L

/-- Equal as unordered edges. -/
def sameE (e f : Edge) : Bool := (e.1 == f.1 && e.2 == f.2) || (e.1 == f.2 && e.2 == f.1)

/-- No two edges of the list are equal as unordered edges. -/
def nodupE : List Edge → Bool
  | [] => true
  | e :: L => L.all (fun f => !sameE e f) && nodupE L

/-- No point occurs twice. -/
def nodupPts : List (List Int) → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupPts xs

/-! ## Exclusion witnesses -/

/-- A witness for excluding a window. `useE = true`: an alternative to the whole window (rules (M), (P_M));
`useE = false`: an alternative to its C-edges (rules (J), (P_J)). `alt` lists the alternative's edges as
(start point, direction). -/
structure Wit where
  useE : Bool
  alt : List (List Int × Nat)
  deriving Inhabited

/-- The edges of an alternative. -/
def altEdges (n : Nat) (alt : List (List Int × Nat)) : List Edge :=
  alt.map (fun a => (a.1, addP a.1 (vecOf n a.2)))

/-- The witness check: the alternative consists of unit steps inside the bounding box of the window, has the degree
parity of the window (`useE`) or of its C-edges, and is shorter, or as long and of smaller `Φ` without repeated
edges. -/
def checkW (n : Nat) (c : List Int) (w : List (Nat × Bool)) (W : Wit) : Bool :=
  let pts := walkPts n (zeros n) (w.map Prod.fst)
  let X := cEdges n w
  let Y := if W.useE then eEdges n w else []
  let P := altEdges n W.alt
  W.alt.all (fun a => decide (a.2 < 2 * n) && inBB n pts a.1 && inBB n pts (addP a.1 (vecOf n a.2))) &&
  parOK P (X ++ Y) &&
  (decide (Y.length + P.length < X.length) ||
    (Y.length + P.length == X.length && nodupE P && decide (phiE c Y + phiE c P < phiE c X)))

/-! ## Witness search (untrusted: only its output is checked) -/

/-- The `φ`-increment of direction `s`. -/
def incr (c : List Int) (s : Nat) : Int := if s % 2 = 0 then c.getD (s / 2) 0 else -(c.getD (s / 2) 0)

/-- Insertion into a list sorted by `f`. -/
def insertBy (f : Nat → Int) (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if f x ≤ f y then x :: y :: ys else y :: insertBy f x ys

/-- Insertion sort by `f`. -/
def sortBy (f : Nat → Int) : List Nat → List Nat
  | [] => []
  | x :: xs => insertBy f x (sortBy f xs)

/-- The directions of the canonical (least-`Φ`) geodesic from `a` to `b`: unit steps sorted by `φ`-increment. -/
def geoDirs (n : Nat) (c : List Int) (a b : List Int) : List Nat :=
  sortBy (incr c) ((List.range n).flatMap (fun i =>
    let d := b.getD i 0 - a.getD i 0
    List.replicate d.natAbs (if d > 0 then 2 * i else 2 * i + 1)))

/-- The edges (start, direction) of the walk from `a` along `ds`. -/
def chainAlt (n : Nat) (a : List Int) : List Nat → List (List Int × Nat)
  | [] => []
  | d :: ds => (a, d) :: chainAlt n (addP a (vecOf n d)) ds

/-- ℓ¹ distance. -/
def l1 (a b : List Int) : Nat := (List.zipWith (fun x y => (x - y).natAbs) a b).sum

/-- The points of odd degree in the C-edges of a walk with points `pts` and labels `labs`. -/
def oddVerts (pts : List (List Int)) (labs : List Bool) : Array (List Int) :=
  let m := labs.length
  ((List.range (m + 1)).filter (fun k =>
    ((if k > 0 && labs.getD (k - 1) false then 1 else 0) + (if k < m && labs.getD k false then 1 else 0)) % 2 == 1)
  ).foldl (fun acc k => acc.push (pts.getD k [])) #[]

/-- Reconstruction of the pairs of an optimal matching from the table of last pairs. -/
def recon (best : Array (Nat × Int × Nat × Nat)) : Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, acc => acc
  | fuel + 1, m, acc =>
    if m == 0 then acc else
    let e := best[m]!
    recon best fuel (m - (1 <<< e.2.2.1) - (1 <<< e.2.2.2)) ((e.2.2.1, e.2.2.2) :: acc)

/-- Least-cost, then least-`Φ`, perfect matching of the points `T` (cost: ℓ¹ distance; `Φ`: the canonical geodesic
of each pair), by dynamic programming over subsets. Returns (cost, `Φ`, pairs). -/
def matchDP (n : Nat) (c : List Int) (T : Array (List Int)) : Option (Nat × Int × List (Nat × Nat)) :=
  let t := T.size
  if t % 2 == 1 then none else
  let costT : Array Nat := (List.range (t * t)).foldl (fun acc k => acc.push (l1 T[k / t]! T[k % t]!)) #[]
  let phiT : Array Int := (List.range (t * t)).foldl (fun acc k =>
    let a := T[k / t]!
    let b := T[k % t]!
    acc.push (phiE c (altEdges n (chainAlt n a (geoDirs n c a b))))) #[]
  let N := 1 <<< t
  let INF : Nat := 1 <<< 40
  let init : Array (Nat × Int × Nat × Nat) := (Array.replicate N (INF, 0, 0, 0)).set! 0 (0, 0, 0, 0)
  let best := (List.range N).foldl (fun best m =>
    let e := best[m]!
    if e.1 ≥ INF then best else
    match (List.range t).find? (fun i => (m >>> i) % 2 == 0) with
    | none => best
    | some i =>
      (List.range t).foldl (fun best j =>
        if j ≤ i || (m >>> j) % 2 == 1 then best else
        let m2 := m + (1 <<< i) + (1 <<< j)
        let cc := e.1 + costT[i * t + j]!
        let ff := e.2.1 + phiT[i * t + j]!
        let e2 := best[m2]!
        if cc < e2.1 || (cc == e2.1 && ff < e2.2.1) then best.set! m2 (cc, ff, i, j) else best) best) init
  let ef := best[N - 1]!
  if ef.1 ≥ INF then none else some (ef.1, ef.2.1, recon best t (N - 1) [])

/-- Removes edges in pairs (equal as unordered edges): what remains are the edges of odd multiplicity. -/
def oddAlt (n : Nat) (alt : List (List Int × Nat)) : List (List Int × Nat) :=
  alt.foldl (fun acc a =>
    let e := (a.1, addP a.1 (vecOf n a.2))
    match acc.findIdx? (fun b => sameE (b.1, addP b.1 (vecOf n b.2)) e) with
    | some k => acc.eraseIdx k
    | none => acc ++ [a]) []

/-- The witness search: the C++ generators' tests (M), (P_M), (J), (P_J) ((S) is the case `n_C = 2`, `n_E = 0` of
(P_M)), returning the alternative that excludes the window. -/
def findW (n : Nat) (c : List Int) (w : List (Nat × Bool)) : Option Wit :=
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
    let T := oddVerts pts (w.map Prod.snd)
    match matchDP n c T with
    | none => none
    | some (cost, f, pairs) =>
      if nC > cost || (nC == cost && decide (f < phC)) then
        let alt := pairs.flatMap (fun p => chainAlt n T[p.1]! (geoDirs n c T[p.1]! T[p.2]!))
        some ⟨false, if nC > cost || nodupE (altEdges n alt) then alt else oddAlt n alt⟩
      else none

/-! ## Certificates -/

/-- The parameters of a certificate. Weights are scaled by the common denominator `Q`: `ω_E = wE / Q`,
`ω_C = wC / Q` (for `p = Pn/Pd`, `X = Xn/Xd`: `wE = Pn Xn²`, `wC = (Pd - Pn) Xd²`, `Q = Pd Xd Xn`); `λ = lamN / lamD`;
the start constant is bounded by `K0n / K0d`. -/
structure Params where
  n : Nat
  c : List Int
  K : Nat
  wE : Nat
  wC : Nat
  Q : Nat
  lamN : Nat
  lamD : Nat
  Hmin : Nat
  K0n : Nat
  K0d : Nat

/-- The digit of a labelled step. -/
def digit (x : Nat × Bool) : Nat := 2 * x.1 + (if x.2 then 1 else 0)

/-- The key of a pattern: its digits in base `4n`, first step most significant. -/
def keyOf (n : Nat) (w : List (Nat × Bool)) : Nat := w.foldl (fun k x => k * (4 * n) + digit x) 0

/-- The pattern of `K` steps with key `k`. -/
def decodeKey (n : Nat) : Nat → Nat → List (Nat × Bool)
  | 0, _ => []
  | K + 1, k => decodeKey n K (k / (4 * n)) ++ [((k % (4 * n)) / 2, (k % (4 * n)) % 2 == 1)]

/-- Binary search in a sorted array (only a found index is used, and it is checked). -/
def bsearch (keys : Array Nat) (k : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo + 1 ≥ hi then lo else
    let mid := (lo + hi) / 2
    if keys[mid]! ≤ k then bsearch keys k fuel mid hi else bsearch keys k fuel lo mid

/-- The index of the key `k`, if it is listed. -/
def lookup (keys : Array Nat) (k : Nat) : Option Nat :=
  let i := bsearch keys k 64 0 keys.size
  if i < keys.size && keys[i]! == k then some i else none

/-- The candidate steps: every direction with both labels. -/
def candList (n : Nat) : List (Nat × Bool) := (List.range (2 * n)).flatMap (fun d => [(d, false), (d, true)])

/-- The window `u` is excluded by a witness found by the search and checked. -/
def exclWin (P : Params) (u : List (Nat × Bool)) : Bool :=
  match findW P.n P.c u with
  | some W => checkW P.n P.c u W
  | none => false

/-- Some window of `2..K+1` edges ending with the last edge of `u` is excluded (found and checked). -/
def exclEnding (P : Params) (u : List (Nat × Bool)) : Bool :=
  (List.range (P.K + 2)).any (fun m => decide (2 ≤ m) && decide (m ≤ u.length) && exclWin P (u.drop (u.length - m)))

/-- The walk of `u` from the origin has no repeated point. -/
def selfAvoid (n : Nat) (u : List (Nat × Bool)) : Bool := nodupPts (walkPts n (zeros n) (u.map Prod.fst))

/-- The weighted sum over the successors of the state `s` (`none` if a candidate is neither excluded nor listed). -/
def rowSum (P : Params) (keys Hs : Array Nat) (s : List (Nat × Bool)) : Option Nat :=
  (candList P.n).foldl (fun acc x =>
    match acc with
    | none => none
    | some tot =>
      let u := s ++ [x]
      if !selfAvoid P.n u then some tot
      else match lookup keys (keyOf P.n u.tail) with
        | some j => if exclWin P u then some tot else some (tot + (if x.2 then P.wC else P.wE) * Hs[j]!)
        | none => if exclEnding P u then some tot else none) (some 0)

/-- The row of state `i`: `H_i ≥ Hmin > 0`, and `∑_{successors} ω H ≤ λ H_i` (scaled by `Q lamD`). -/
def rowCheck (P : Params) (keys Hs : Array Nat) (i : Nat) : Bool :=
  let h := Hs[i]!
  decide (0 < P.Hmin) && decide (P.Hmin ≤ h) &&
  match rowSum P keys Hs (decodeKey P.n P.K keys[i]!) with
  | some tot => decide (tot * P.lamD ≤ P.lamN * P.Q * h)
  | none => false

/-- The rows of the states `lo, …, hi - 1`. -/
def rowsOK (P : Params) (keys Hs : Array Nat) (lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all (rowCheck P keys Hs)

/-- Start completeness: every self-avoiding extension of the prefix to `K` steps is excluded by a checked witness
on the way, or is a listed state (`r` = the number of steps still to add). -/
def dfsOK (P : Params) (keys : Array Nat) : Nat → List (Nat × Bool) → Bool
  | 0, pfx => (lookup keys (keyOf P.n pfx)).isSome
  | r + 1, pfx => (candList P.n).all (fun x =>
      let u := pfx ++ [x]
      !selfAvoid P.n u || exclEnding P u || dfsOK P keys r u)

/-- The number of C-labels of the state with key `k`. -/
def nCOf (n K k : Nat) : Nat := ((decodeKey n K k).filter (fun x => x.2)).length

/-- `tot[c]` = the sum of `H` over the states with `c` C-labels. -/
def totByC (P : Params) (keys Hs : Array Nat) : Array Nat :=
  (List.range keys.size).foldl (fun acc i =>
    let c := nCOf P.n P.K keys[i]!
    acc.set! c (acc[c]! + Hs[i]!)) (Array.replicate (P.K + 1) 0)

/-- The start-sum bound: `(ω_E + ω_C)² ∑_s ω(s) H(s) ≤ (K0n / K0d) Hmin`, scaled by `Q^(K+2) K0d`. -/
def startOK (P : Params) (keys Hs : Array Nat) : Bool :=
  let tot := totByC P keys Hs
  let S := (List.range (P.K + 1)).foldl (fun acc c => acc + tot[c]! * P.wE ^ (P.K - c) * P.wC ^ c) 0
  decide ((P.wE + P.wC) ^ 2 * S * P.K0d ≤ P.K0n * P.Hmin * P.Q ^ (P.K + 2))

end QECComp
