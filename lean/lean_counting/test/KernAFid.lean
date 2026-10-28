import QECCountComp.KernA
import QECCountComp.Data.AH5
import QECCountComp.Data.AH6F

/-!
# Fidelity of the kernel augmented search on AH5 and AH6F (compiled evaluation, a test; not part of any proof)

For every near row and the two rows of every bulk state, every candidate step: `exclWinA` against `exclWinAK` (listed
successors) and `exclEndingA` against `exclEndingAK` (unlisted successors); and at every node of the start search from
every start height: `exclEndingA` against `exclEndingAK`. Prints the numbers of comparisons and mismatches.
-/

open QECComp QECComp.Data

def addNN (a b : Nat × Nat) : Nat × Nat := (a.1 + b.1, a.2 + b.2)

def fidRowA (P : ParamsA) (nk nG bk bH : Array Nat) (s : List (Nat × Bool)) (h : Int) : Nat × Nat :=
  (candList 2).foldl (fun acc x =>
    let u := s ++ [x]
    let h0 := h + vdisp s
    let h2 := h - dl2 x.1
    if !selfAvoid 2 u || decide (h2 < 0) then acc
    else match potA P nk nG bk bH u.tail h2 with
      | some _ => (acc.1 + 1, if exclWinA P h0 u == exclWinAK P h0 u then acc.2 else acc.2 + 1)
      | none => (acc.1 + 1, if exclEndingA P h0 u == exclEndingAK P h0 u then acc.2 else acc.2 + 1)) (0, 0)

def fidRowsA (P : ParamsA) (nk nG bk bH : Array Nat) : Nat × Nat :=
  let a := (List.range nk.size).foldl (fun acc i =>
    let k := nk[i]!
    addNN acc (fidRowA P nk nG bk bH (decodeA P.K k) ((heightOf P.K k : Nat) : Int))) (0, 0)
  (List.range bk.size).foldl (fun acc j =>
    let s := decodeA P.K bk[j]!
    addNN (addNN acc (fidRowA P nk nG bk bH s bigH)) (fidRowA P nk nG bk bH s P.HC)) a

def fidDfsA (P : ParamsA) (h0 : Int) : Nat → List (Nat × Bool) → Nat × Nat
  | 0, _ => (0, 0)
  | r + 1, pfx => (candList 2).foldl (fun acc x =>
      let u := pfx ++ [x]
      if !selfAvoid 2 u || decide (h0 - vdisp u < 0) then acc
      else
        let a := exclEndingA P h0 u
        let b := exclEndingAK P h0 u
        let acc := (acc.1 + 1, if a == b then acc.2 else acc.2 + 1)
        if a then acc else addNN acc (fidDfsA P h0 r u)) (0, 0)

def fidStartsA (P : ParamsA) : Nat × Nat :=
  (List.range (P.HC + P.K + 2)).foldl (fun acc i => addNN acc (fidDfsA P (offA P i) P.K [])) (0, 0)

#eval fidRowsA PAH5 nkAH5 nGAH5 bkAH5 bHAH5
#eval fidStartsA PAH5
#eval fidRowsA PAH6F nkAH6F nGAH6F bkAH6F bHAH6F
#eval fidStartsA PAH6F
