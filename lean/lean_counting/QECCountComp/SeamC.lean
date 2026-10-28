import QECCountComp.Core

/-!
# Seam-aware certificate checks for the toric code (dimension 2)

On the torus the tie-break function is `φ = x_rep`, the representative of `x` in `[0, L)`; it jumps at the seam
between `x = L - 1` and `x = 0`. The seam offset of a column is `q = x` near `x = 0` and `q = x - L` near `x = L - 1`, so
the seam lies between `q = -1` and `q = 0`, and `φ_true(q) = q` for `q ≥ 0`, `L + q` for `q < 0`: the pair
`(A, B) = (1, q)` or `(0, q)` stands for `L·A + B`. `checkWT L0 o w W` is `checkW` (dimension 2) for a window whose
first vertex has seam offset `o`, with the true `Φ` in the tie case, compared lexicographically; it checks
`|ΔB| < L0`, so that the comparison is the comparison of the integers `L·A + B` for every `L ≥ L0`.

A far window (all its points on one side of the seam) gives the same answers at every offset of that side as at the
offset `bigO` (no `L` terms, `φ = x` up to a constant): the bulk rules with `φ = x`.

The certificate: near states (pattern, head offset `o` with `-HC ≤ o ≤ HC - 1`) with potentials `G`, and bulk states
(pattern) with potentials `Hb`. A state's potential is `G` if its head offset is near, `Hb` otherwise. Rows: near
rows, the two interface rows (head offset `HC` and `-HC - 1`, bulk patterns), the bulk rows (offset `bigO`).
-/

namespace QECComp

/-- An offset far to the right of the seam, standing for every far offset. -/
def bigO : Int := 1000000

/-- `φ_true` of a seam offset: `(A, B)` for `L·A + B`. -/
def phiT (q : Int) : Int × Int := if q < 0 then (1, q) else (0, q)

/-- Sum of pairs. -/
def addPair (a b : Int × Int) : Int × Int := (a.1 + b.1, a.2 + b.2)

/-- The true `Φ` of an edge list of a window whose first vertex has seam offset `o` (`φ` depends on `x` only). -/
def phiTE (o : Int) : List Edge → Int × Int
  | [] => (0, 0)
  | e :: L => addPair (addPair (phiT (o + e.1.getD 0 0)) (phiT (o + e.2.getD 0 0))) (phiTE o L)

/-- Lexicographic order on `(A, B)`. -/
def lexLt (a b : Int × Int) : Bool := decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 < b.2))

/-- The seam witness check. -/
def checkWT (L0 : Nat) (o : Int) (w : List (Nat × Bool)) (W : Wit) : Bool :=
  let pts := walkPts 2 (zeros 2) (w.map Prod.fst)
  let X := cEdges 2 w
  let Y := if W.useE then eEdges 2 w else []
  let P := altEdges 2 W.alt
  let lhs := addPair (phiTE o Y) (phiTE o P)
  let rhs := phiTE o X
  W.alt.all (fun a => decide (a.2 < 4) && inBB 2 pts a.1 && inBB 2 pts (addP a.1 (vecOf 2 a.2))) &&
  parOK P (X ++ Y) &&
  (decide (Y.length + P.length < X.length) ||
    (Y.length + P.length == X.length && nodupE P && lexLt lhs rhs && decide ((rhs.2 - lhs.2).natAbs < L0)))

/-! ## Search (untrusted) -/

/-- Lexicographic minimum of two `(A, B)` pairs with payloads. -/
def lexMin {α : Type} (a b : (Int × Int) × α) : (Int × Int) × α := if lexLt b.1 a.1 then b else a

/-- The least true-`Φ` monotone path from `a` to `b` (window coordinates; seam offset `o + x`), as directions. -/
def dpPathT (o : Int) (a b : List Int) : (Int × Int) × List Nat :=
  let dx := b.getD 0 0 - a.getD 0 0
  let dy := b.getD 1 0 - a.getD 1 0
  let nx := dx.natAbs
  let ny := dy.natAbs
  let sx : Int := if dx ≥ 0 then 1 else -1
  let stx : Nat := if dx ≥ 0 then 0 else 1
  let sty : Nat := if dy ≥ 0 then 2 else 3
  let W := ny + 1
  let INF : Int × Int := (1000000000, 0)
  let phx (i : Nat) : Int × Int := phiT (o + a.getD 0 0 + sx * i)
  let init : Array ((Int × Int) × Nat) := (Array.replicate ((nx + 1) * W) (INF, 0)).set! 0 ((0, 0), 0)
  let best := (List.range ((nx + 1) * W)).foldl (fun best k =>
    let i := k / W
    let j := k % W
    if k == 0 then best else
    let fromX : (Int × Int) × Nat := if i > 0 then
        (let e := best[(i - 1) * W + j]!; (addPair e.1 (addPair (phx (i - 1)) (phx i)), 0)) else (INF, 0)
    let fromY : (Int × Int) × Nat := if j > 0 then
        (let e := best[i * W + (j - 1)]!; (addPair e.1 (addPair (phx i) (phx i)), 1)) else (INF, 1)
    best.set! k (lexMin fromX fromY)) init
  let rec back (fuel i j : Nat) (acc : List Nat) : List Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if i == 0 && j == 0 then acc else
      let e := best[i * W + j]!
      if e.2 == 0 then back fuel (i - 1) j (stx :: acc) else back fuel i (j - 1) (sty :: acc)
  (best[nx * W + ny]!.1, back (nx + ny + 1) nx ny [])

/-- Least-cost, then least true-`Φ`, perfect matching by dynamic programming over subsets. -/
def matchDPT (o : Int) (T : Array (List Int)) : Option (Nat × (Int × Int) × List (Nat × Nat)) :=
  let t := T.size
  if t % 2 == 1 then none else
  let costT : Array Nat := (List.range (t * t)).foldl (fun acc k => acc.push (l1 T[k / t]! T[k % t]!)) #[]
  let phiTT : Array (Int × Int) := (List.range (t * t)).foldl (fun acc k =>
    acc.push (dpPathT o T[k / t]! T[k % t]!).1) #[]
  let N := 1 <<< t
  let INF : Nat := 1 <<< 40
  let init : Array (Nat × (Int × Int) × Nat × Nat) := (Array.replicate N (INF, (0, 0), 0, 0)).set! 0 (0, (0, 0), 0, 0)
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
        let ff := addPair e.2.1 phiTT[i * t + j]!
        let e2 := best[m2]!
        if cc < e2.1 || (cc == e2.1 && lexLt ff e2.2.1) then best.set! m2 (cc, ff, i, j) else best) best) init
  let ef := best[N - 1]!
  if ef.1 ≥ INF then none else
  let rec recon2 (fuel m : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if m == 0 then acc else
      let e := best[m]!
      recon2 fuel (m - (1 <<< e.2.2.1) - (1 <<< e.2.2.2)) ((e.2.2.1, e.2.2.2) :: acc)
  some (ef.1, ef.2.1, recon2 t (N - 1) [])

/-- The seam witness search (tm2d_seam's `excluded_t`: (M), (P_M), (J), (P_J); (S) is a case of (P_M)). -/
def findWT (o : Int) (w : List (Nat × Bool)) : Option Wit :=
  let pts := walkPts 2 (zeros 2) (w.map Prod.fst)
  let X := cEdges 2 w
  let Y := eEdges 2 w
  let nC := X.length
  let nE := Y.length
  let a := zeros 2
  let b := pts.getLastD a
  let dist := l1 a b
  let g := dpPathT o a b
  let geo := chainAlt 2 a g.2
  let phC := phiTE o X
  if nC > nE + dist then some ⟨true, geo⟩
  else if nC > 0 && nC == nE + dist && lexLt (addPair (phiTE o Y) g.1) phC then some ⟨true, geo⟩
  else if nC < 2 then none
  else
    let T := oddVerts pts (w.map Prod.snd)
    match matchDPT o T with
    | none => none
    | some (cost, f, pairs) =>
      if nC > cost || (nC == cost && lexLt f phC) then
        let alt := pairs.flatMap (fun pr => chainAlt 2 T[pr.1]! (dpPathT o T[pr.1]! T[pr.2]!).2)
        some ⟨false, if nC > cost || nodupE (altEdges 2 alt) then alt else oddAlt 2 alt⟩
      else none

/-! ## The seam certificate -/

/-- Parameters of a seam certificate (dimension 2, `φ = x`): memory `K`, near range `HC`, `L0`, scaled weights,
`λ`, `Hmin`, start constant bound. -/
structure ParamsT where
  K : Nat
  HC : Nat
  L0 : Nat
  wE : Nat
  wC : Nat
  Q : Nat
  lamN : Nat
  lamD : Nat
  Hmin : Nat
  K0n : Nat
  K0d : Nat

/-- The window `u`, whose first vertex has seam offset `o`, is excluded (found and checked). -/
def exclWinT (P : ParamsT) (o : Int) (u : List (Nat × Bool)) : Bool :=
  match findWT o u with
  | some W => checkWT P.L0 o u W
  | none => false

/-- The x-coordinate displacement of a pattern. -/
def xdisp (w : List (Nat × Bool)) : Int :=
  w.foldl (fun s x => s + (if x.1 == 0 then 1 else if x.1 == 1 then -1 else 0)) 0

/-- Some window of `2..K+1` edges ending with the last edge of `u` is excluded; `o` is the seam offset of the first
vertex of `u`. -/
def exclEndingT (P : ParamsT) (o : Int) (u : List (Nat × Bool)) : Bool :=
  (List.range (P.K + 2)).any (fun m => decide (2 ≤ m) && decide (m ≤ u.length) &&
    exclWinT P (o + xdisp (u.take (u.length - m))) (u.drop (u.length - m)))

/-- The key of a near state: pattern key, then the head offset. -/
def nearKey (σ : List (Nat × Bool)) (o : Int) : Nat := keyOf 2 σ * 4096 + (o + 2048).toNat

/-- The potential of the state `(σ, o)` (head offset `o`): `G` if near and listed, `Hb` if far and listed. -/
def potT (P : ParamsT) (nk nG bk bH : Array Nat) (σ : List (Nat × Bool)) (o : Int) : Option Nat :=
  if -(P.HC : Int) ≤ o ∧ o < P.HC then (lookup nk (nearKey σ o)).map (fun j => nG[j]!)
  else (lookup bk (keyOf 2 σ)).map (fun j => bH[j]!)

/-- The weighted sum over the successors of the state `(s, o)` (head offset `o`). -/
def rowSumT (P : ParamsT) (nk nG bk bH : Array Nat) (s : List (Nat × Bool)) (o : Int) : Option Nat :=
  (candList 2).foldl (fun acc x =>
    match acc with
    | none => none
    | some tot =>
      let u := s ++ [x]
      let o0 := o - xdisp s
      if !selfAvoid 2 u then some tot
      else match potT P nk nG bk bH u.tail (o + xdisp [x]) with
        | some h => if exclWinT P o0 u then some tot else some (tot + (if x.2 then P.wC else P.wE) * h)
        | none => if exclEndingT P o0 u then some tot else none) (some 0)

/-- A row: `Hmin ≤ h` and the weighted successor sum is at most `λ h`. -/
def rowOKT (P : ParamsT) (nk nG bk bH : Array Nat) (s : List (Nat × Bool)) (o : Int) (h : Nat) : Bool :=
  decide (0 < P.Hmin) && decide (P.Hmin ≤ h) &&
  match rowSumT P nk nG bk bH s o with
  | some tot => decide (tot * P.lamD ≤ P.lamN * P.Q * h)
  | none => false

/-- The near rows of the entries `lo, …, hi - 1`. -/
def nearRowsOK (P : ParamsT) (nk nG bk bH : Array Nat) (lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all (fun i =>
    let k := nk[i]!
    rowOKT P nk nG bk bH (decodeKey 2 P.K (k / 4096)) ((k % 4096 : Nat) - 2048 : Int) nG[i]!)

/-- The bulk rows of the entries `lo, …, hi - 1`, at the offsets `bigO`, `HC` and `-HC - 1`. -/
def bulkRowsOK (P : ParamsT) (nk nG bk bH : Array Nat) (lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all (fun i =>
    let s := decodeKey 2 P.K bk[i]!
    rowOKT P nk nG bk bH s bigO bH[i]! && rowOKT P nk nG bk bH s P.HC bH[i]! &&
      rowOKT P nk nG bk bH s (-(P.HC : Int) - 1) bH[i]!)

/-- Start completeness from a first vertex with seam offset `o0`: every self-avoiding extension to `K` steps is
excluded on the way or is a listed state. -/
def dfsT (P : ParamsT) (nk nG bk bH : Array Nat) (o0 : Int) : Nat → List (Nat × Bool) → Bool
  | 0, pfx => (potT P nk nG bk bH pfx (o0 + xdisp pfx)).isSome
  | r + 1, pfx => (candList 2).all (fun x =>
      let u := pfx ++ [x]
      !selfAvoid 2 u || exclEndingT P o0 u || dfsT P nk nG bk bH o0 r u)

/-- Start completeness from the offsets `bigO` and `-HC - K, …, HC + K - 1`, by the first step. -/
def dfsTopT (P : ParamsT) (nk nG bk bH : Array Nat) (o0 : Int) (j : Nat) : Bool :=
  match (candList 2)[j]? with
  | some x => !selfAvoid 2 [x] || exclEndingT P o0 [x] || dfsT P nk nG bk bH o0 (P.K - 1) [x]
  | none => true

/-- Start completeness from the offset `o0`, every first step. -/
def dfsOffT (P : ParamsT) (nk nG bk bH : Array Nat) (o0 : Int) : Bool :=
  (List.range (candList 2).length).all (dfsTopT P nk nG bk bH o0)

/-- `f` holds at the `cnt` integers from `lo`. -/
def rangeAllT (lo : Int) (cnt : Nat) (f : Int → Bool) : Bool := (List.range cnt).all (fun i => f (lo + i))

/-- The start sum from a first vertex with seam offset `o0` (scaled by `Q^K`): the listed states whose first vertex
has offset `o0`, i.e. near states `(σ, o)` with `o - xdisp σ = o0` and bulk states whose head offset
`o0 + xdisp σ` is far. -/
def startSumT (P : ParamsT) (nk nG bk bH : Array Nat) (o0 : Int) : Nat :=
  let wt (σ : List (Nat × Bool)) : Nat :=
    let c := (σ.filter (fun x => x.2)).length
    P.wE ^ (P.K - c) * P.wC ^ c
  let sn := (List.range nk.size).foldl (fun acc i =>
    let k := nk[i]!
    let σ := decodeKey 2 P.K (k / 4096)
    let o : Int := (k % 4096 : Nat) - 2048
    if o - xdisp σ == o0 then acc + wt σ * nG[i]! else acc) 0
  let sb := (List.range bk.size).foldl (fun acc j =>
    let σ := decodeKey 2 P.K bk[j]!
    let oh := o0 + xdisp σ
    if -(P.HC : Int) ≤ oh ∧ oh < P.HC then acc else acc + wt σ * bH[j]!) 0
  sn + sb

/-- The start bound from the offset `o0`: `(ω_E + ω_C) · S(o0) / Hmin ≤ K0n / K0d` (one factor for the closing edge
of the cycle), scaled by `Q^(K+1) K0d`. -/
def startOKT (P : ParamsT) (nk nG bk bH : Array Nat) (o0 : Int) : Bool :=
  decide ((P.wE + P.wC) * startSumT P nk nG bk bH o0 * P.K0d ≤ P.K0n * P.Hmin * P.Q ^ (P.K + 1))

end QECComp
