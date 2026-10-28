import QECCountComp.Core

/-!
# Loading certificate data; chunks of the start check

A certificate's states are stored as strings of fixed-width hexadecimal records: 7 digits of the key, then 9 digits
of the potential `H` (lower-case digits). `loadData` turns the chunks into the arrays of keys and potentials.
Nothing here needs to be trusted: the keys are only used through checked equalities, and the potentials are the
numbers whose rows are checked.

`dfsTop P keys j` is the part of `dfsOK P keys P.K []` that starts with the `j`-th candidate step.
-/

namespace QECComp

/-- The value of a lower-case hexadecimal digit. -/
def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87

/-- The state of the record parser. -/
structure PState where
  pos : Nat
  k : Nat
  h : Nat
  keys : Array Nat
  hs : Array Nat

/-- One character of the record parser. -/
def stepP (st : PState) (c : Char) : PState :=
  let v := hexVal c
  if st.pos < 7 then { st with pos := st.pos + 1, k := st.k * 16 + v }
  else if st.pos < 15 then { st with pos := st.pos + 1, h := st.h * 16 + v }
  else { pos := 0, k := 0, h := 0, keys := st.keys.push st.k, hs := st.hs.push (st.h * 16 + v) }

/-- The arrays of keys and potentials of the records in the chunks. -/
def loadData (chunks : List String) : Array Nat × Array Nat :=
  let st := chunks.foldl (fun st s => s.foldl stepP st) ⟨0, 0, 0, #[], #[]⟩
  (st.keys, st.hs)

/-- The part of the start check that begins with the `j`-th candidate step. -/
def dfsTop (P : Params) (keys : Array Nat) (j : Nat) : Bool :=
  match (candList P.n)[j]? with
  | some x => !selfAvoid P.n [x] || exclEnding P [x] || dfsOK P keys (P.K - 1) [x]
  | none => true

end QECComp
