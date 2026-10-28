import QECCountComp.KernT
import QECCountComp.Data.T5

/-!
# Fidelity of the kernel seam search on T5 (compiled evaluation, a test; not part of any proof)

For every near row and the three rows of every bulk state of T5, every candidate step: `exclWinT` against `exclWinTK`
(listed successors) and `exclEndingT` against `exclEndingTK` (unlisted successors); and at every node of the start
search from every start offset: `exclEndingT` against `exclEndingTK`. Prints the numbers of comparisons and mismatches.
-/

open QECComp QECComp.Data

def fidRow (P : ParamsT) (nk nG bk bH : Array Nat) (s : List (Nat × Bool)) (o : Int) : Nat × Nat :=
  (candList 2).foldl (fun acc x =>
    let u := s ++ [x]
    let o0 := o - xdisp s
    if !selfAvoid 2 u then acc
    else match potT P nk nG bk bH u.tail (o + xdisp [x]) with
      | some _ => (acc.1 + 1, if exclWinT P o0 u == exclWinTK P o0 u then acc.2 else acc.2 + 1)
      | none => (acc.1 + 1, if exclEndingT P o0 u == exclEndingTK P o0 u then acc.2 else acc.2 + 1)) (0, 0)

def addNN (a b : Nat × Nat) : Nat × Nat := (a.1 + b.1, a.2 + b.2)

def fidRows (P : ParamsT) (nk nG bk bH : Array Nat) : Nat × Nat :=
  let a := (List.range nk.size).foldl (fun acc i =>
    let k := nk[i]!
    addNN acc (fidRow P nk nG bk bH (decodeKey 2 P.K (k / 4096)) ((k % 4096 : Nat) - 2048 : Int))) (0, 0)
  (List.range bk.size).foldl (fun acc j =>
    let s := decodeKey 2 P.K bk[j]!
    addNN (addNN (addNN acc (fidRow P nk nG bk bH s bigO)) (fidRow P nk nG bk bH s P.HC))
      (fidRow P nk nG bk bH s (-(P.HC : Int) - 1))) a

def fidDfs (P : ParamsT) (o0 : Int) : Nat → List (Nat × Bool) → Nat × Nat
  | 0, _ => (0, 0)
  | r + 1, pfx => (candList 2).foldl (fun acc x =>
      let u := pfx ++ [x]
      if !selfAvoid 2 u then acc
      else
        let a := exclEndingT P o0 u
        let b := exclEndingTK P o0 u
        let acc := (acc.1 + 1, if a == b then acc.2 else acc.2 + 1)
        if a then acc else addNN acc (fidDfs P o0 r u)) (0, 0)

def fidStarts (P : ParamsT) : Nat × Nat :=
  (List.range (2 * (P.HC + P.K) + 1)).foldl (fun acc i => addNN acc (fidDfs P (offT P i) P.K [])) (0, 0)

#eval fidRows PT5 nkT5 nGT5 bkT5 bHT5
#eval fidStarts PT5
