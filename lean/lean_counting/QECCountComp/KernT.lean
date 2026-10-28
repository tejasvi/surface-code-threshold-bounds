import QECCountComp.SeamC
import QECCountComp.Kern2

/-!
# Kernel route for the seam certificates (toric code)

The checks of `SeamC.lean`, written for evaluation by the kernel (`decide +kernel`):

* the listed states are reached through two lookup functions `fN fB : Nat → Option (Nat × Nat)`, near states by
  `nearKey σ o`, bulk states by `keyOf 2 σ`, each returning (potential, mask); for a tree store, `fN = tN.find`. A
  near mask marks the candidate steps whose listed successor the generator found excluded (full window); a bulk
  entry carries three masks `m₀ + 256 m₁ + 65536 m₂`, for the offsets `bigO`, `HC`, `-HC - 1`. A mask is only a hint:
  every claimed exclusion is found again and checked (`exclWinTK`), and an unmarked candidate with a listed target
  simply enters the row;
* the witness search `findWTK` is `findWT` with the least true-`Φ` monotone path in closed form (`pathTK`) and the
  matching found by recursion (`matchRecT`); it is untrusted, its output is checked by `checkWT`;
* start completeness tries the extension before the exclusion search (`dfsTK`), so that legal prefixes never pay for a
  failed search;
* the start sums are sums over the entries (`nearContribT`, `bulkContribT`), one per start offset `offT P i`.
-/

namespace QECComp

/-- The least true-`Φ` monotone path from `a` to `b` (window coordinates, seam offset `o + x`): the horizontal steps to
the column of least `φ_true`, all vertical steps there, then the horizontal steps to `b`. `φ_true` takes distinct
values on distinct columns, so this is the unique least path (the path of `dpPathT`). Returns its `Φ` and its
directions. -/
def pathTK (o : Int) (a b : List Int) : (Int × Int) × List Nat :=
  let ax := a.getD 0 0
  let dx := b.getD 0 0 - ax
  let dy := b.getD 1 0 - a.getD 1 0
  let nx := dx.natAbs
  let ny := dy.natAbs
  let sx : Int := if dx ≥ 0 then 1 else -1
  let stx : Nat := if dx ≥ 0 then 0 else 1
  let sty : Nat := if dy ≥ 0 then 2 else 3
  let phx (i : Nat) : Int × Int := phiT (o + ax + sx * i)
  let ic := (List.range (nx + 1)).foldl (fun best i => if lexLt (phx i) (phx best) then i else best) 0
  let hor := (List.range nx).foldl (fun acc i => addPair acc (addPair (phx i) (phx (i + 1)))) (0, 0)
  let ver := (List.range ny).foldl (fun acc _ => addPair acc (addPair (phx ic) (phx ic))) (0, 0)
  (addPair hor ver, List.replicate ic stx ++ List.replicate ny sty ++ List.replicate (nx - ic) stx)

/-- Least-cost, then least true-`Φ`, perfect matching by recursion: the first point is paired with each other point. -/
def matchRecT (o : Int) : Nat → List (List Int) → Option (Nat × (Int × Int) × List (List Int × List Int))
  | 0, _ => none
  | _, [] => some (0, (0, 0), [])
  | fuel + 1, a :: rest =>
    rest.foldl (fun best b =>
      match matchRecT o fuel (rest.erase b) with
      | none => best
      | some (cc, ff, ps) =>
        let cost := cc + l1 a b
        let phi := addPair ff (pathTK o a b).1
        match best with
        | none => some (cost, phi, (a, b) :: ps)
        | some (bc, bf, _) => if cost < bc || (cost == bc && lexLt phi bf) then some (cost, phi, (a, b) :: ps)
            else best) none

/-- The seam witness search of `findWT`, with `pathTK` and `matchRecT` (untrusted). -/
def findWTK (o : Int) (w : List (Nat × Bool)) : Option Wit :=
  let pts := walkPts 2 (zeros 2) (w.map Prod.fst)
  let X := cEdges 2 w
  let Y := eEdges 2 w
  let nC := X.length
  let nE := Y.length
  let a := zeros 2
  let b := pts.getLastD a
  let dist := l1 a b
  let g := pathTK o a b
  let geo := chainAlt 2 a g.2
  let phC := phiTE o X
  if nC > nE + dist then some ⟨true, geo⟩
  else if nC > 0 && nC == nE + dist && lexLt (addPair (phiTE o Y) g.1) phC then some ⟨true, geo⟩
  else if nC < 2 then none
  else
    let T := oddVertsL pts (w.map Prod.snd)
    match matchRecT o (T.length + 1) T with
    | none => none
    | some (cost, f, pairs) =>
      if nC > cost || (nC == cost && lexLt f phC) then
        let alt := pairs.flatMap (fun pr => chainAlt 2 pr.1 (pathTK o pr.1 pr.2).2)
        some ⟨false, if nC > cost || nodupE (altEdges 2 alt) then alt else oddAlt 2 alt⟩
      else none

/-- The window `u`, whose first vertex has seam offset `o`, is excluded by a witness found by `findWTK` and checked. -/
def exclWinTK (P : ParamsT) (o : Int) (u : List (Nat × Bool)) : Bool :=
  match findWTK o u with
  | some W => checkWT P.L0 o u W
  | none => false

/-- Some window of `2..K+1` edges ending with the last edge of `u` is excluded (as `exclEndingT`, with
`exclWinTK`). -/
def exclEndingTK (P : ParamsT) (o : Int) (u : List (Nat × Bool)) : Bool :=
  (List.range (P.K + 2)).any (fun m => decide (2 ≤ m) && decide (m ≤ u.length) &&
    exclWinTK P (o + xdisp (u.take (u.length - m))) (u.drop (u.length - m)))

/-- The potential and mask of the state `(σ, o)` (head offset `o`): from the near store if `-HC ≤ o < HC`, from the
bulk store otherwise. -/
def potTK (P : ParamsT) (fN fB : Nat → Option (Nat × Nat)) (σ : List (Nat × Bool)) (o : Int) : Option (Nat × Nat) :=
  if -(P.HC : Int) ≤ o ∧ o < P.HC then fN (nearKey σ o) else fB (keyOf 2 σ)

/-- The weighted sum over the successors of the state `(s, o)` with mask `mask` (`none` if a candidate is neither
excluded nor listed, or a claimed exclusion fails). -/
def rowSumTK (P : ParamsT) (fN fB : Nat → Option (Nat × Nat)) (mask : Nat) (s : List (Nat × Bool)) (o : Int) :
    Option Nat :=
  ((candList 2).zip (List.range 8)).foldl (fun acc xi =>
    match acc with
    | none => none
    | some tot =>
      let u := s ++ [xi.1]
      let o0 := o - xdisp s
      if !selfAvoid 2 u then some tot
      else match potTK P fN fB u.tail (o + xdisp [xi.1]) with
        | some hm =>
          if mask / 2 ^ xi.2 % 2 == 1 then (if exclWinTK P o0 u then some tot else none)
          else some (tot + (if xi.1.2 then P.wC else P.wE) * hm.1)
        | none => if exclEndingTK P o0 u then some tot else none) (some 0)

/-- A row: `Hmin ≤ h` and the weighted successor sum is at most `λ h`. -/
def rowCheckTK (P : ParamsT) (fN fB : Nat → Option (Nat × Nat)) (mask : Nat) (s : List (Nat × Bool)) (o : Int)
    (h : Nat) : Bool :=
  decide (0 < P.Hmin) && decide (P.Hmin ≤ h) &&
  match rowSumTK P fN fB mask s o with
  | some tot => decide (tot * P.lamD ≤ P.lamN * P.Q * h)
  | none => false

/-- The row of a near entry `(nearKey σ o, G, mask)`. -/
def nearRowTK (P : ParamsT) (fN fB : Nat → Option (Nat × Nat)) (e : Nat × Nat × Nat) : Bool :=
  rowCheckTK P fN fB e.2.2 (decodeKey 2 P.K (e.1 / 4096)) ((e.1 % 4096 : Nat) - 2048 : Int) e.2.1

/-- The three rows of a bulk entry `(keyOf 2 σ, Hb, masks)`: at the offsets `bigO`, `HC` and `-HC - 1`. -/
def bulkRowTK (P : ParamsT) (fN fB : Nat → Option (Nat × Nat)) (e : Nat × Nat × Nat) : Bool :=
  let s := decodeKey 2 P.K e.1
  rowCheckTK P fN fB (e.2.2 % 256) s bigO e.2.1 && rowCheckTK P fN fB (e.2.2 / 256 % 256) s P.HC e.2.1 &&
    rowCheckTK P fN fB (e.2.2 / 65536 % 256) s (-(P.HC : Int) - 1) e.2.1

/-- Start completeness from a first vertex with seam offset `o0` (as `dfsT`, the extension tried first). -/
def dfsTK (P : ParamsT) (fN fB : Nat → Option (Nat × Nat)) (o0 : Int) : Nat → List (Nat × Bool) → Bool
  | 0, pfx => (potTK P fN fB pfx (o0 + xdisp pfx)).isSome
  | r + 1, pfx => (candList 2).all (fun x =>
      let u := pfx ++ [x]
      !selfAvoid 2 u || dfsTK P fN fB o0 r u || exclEndingTK P o0 u)

/-- The start check from the offset `o0` for the walks that continue the prefix `pfx` with the candidate steps of
indices `js`, then with any `K - |pfx| - |js|` further steps. -/
def dfsPreTK (P : ParamsT) (fN fB : Nat → Option (Nat × Nat)) (o0 : Int) : List Nat → List (Nat × Bool) → Bool
  | [], pfx => dfsTK P fN fB o0 (P.K - pfx.length) pfx
  | j :: js, pfx =>
    match (candList 2)[j]? with
    | some x =>
      let u := pfx ++ [x]
      !selfAvoid 2 u || dfsPreTK P fN fB o0 js u || exclEndingTK P o0 u
    | none => true

/-- The weight `ω_E^{K-c} ω_C^c` of a pattern with `c` C-labels (scaled by `Q^K`). -/
def wtT (P : ParamsT) (σ : List (Nat × Bool)) : Nat :=
  let c := (σ.filter (fun x => x.2)).length
  P.wE ^ (P.K - c) * P.wC ^ c

/-- The start offsets by index: `-HC - K + i` for `i < 2 (HC + K)`, then `bigO`. -/
def offT (P : ParamsT) (i : Nat) : Int := if i < 2 * (P.HC + P.K) then -((P.HC + P.K : Nat) : Int) + i else bigO

/-- The contributions of a near entry to the start sums of the offsets `offT P i`, `i ≤ 2 (HC + K)`. -/
def nearContribT (P : ParamsT) (e : Nat × Nat × Nat) : List Nat :=
  let σ := decodeKey 2 P.K (e.1 / 4096)
  let o : Int := (e.1 % 4096 : Nat) - 2048
  (List.range (2 * (P.HC + P.K) + 1)).map (fun i => if o - xdisp σ == offT P i then wtT P σ * e.2.1 else 0)

/-- The contributions of a bulk entry to the start sums: every offset from which its head offset is far. -/
def bulkContribT (P : ParamsT) (e : Nat × Nat × Nat) : List Nat :=
  let σ := decodeKey 2 P.K e.1
  (List.range (2 * (P.HC + P.K) + 1)).map (fun i =>
    let oh := offT P i + xdisp σ
    if -(P.HC : Int) ≤ oh ∧ oh < P.HC then 0 else wtT P σ * e.2.1)

/-- The pointwise sum of a list of lists (`addL`). -/
def sumL : List (List Nat) → List Nat
  | [] => []
  | x :: xs => addL x (sumL xs)

/-- The sums over the entries of a tree, `f` the contributions of an entry (pointwise, with `addL`). -/
def totTK (f : Nat × Nat × Nat → List Nat) : KTree → List Nat
  | .leaf => []
  | .node l k h m r => addL (totTK f l) (addL (f (k, h, m)) (totTK f r))

/-- The start bounds from the near and bulk totals (as `startOKT`, at every offset `offT P i`). -/
def startOKTK (P : ParamsT) (totN totB : List Nat) : Bool :=
  (List.range (2 * (P.HC + P.K) + 1)).all (fun i =>
    decide ((P.wE + P.wC) * (totN.getD i 0 + totB.getD i 0) * P.K0d ≤ P.K0n * P.Hmin * P.Q ^ (P.K + 1)))

end QECComp
