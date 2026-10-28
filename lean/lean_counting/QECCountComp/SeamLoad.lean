import QECCountComp.Load

/-!
# Loading seam certificate data

Records of fixed width: `kw` hexadecimal digits of the key, then `hw` digits of the potential (lower-case digits).
Nothing here needs to be trusted: keys are only used through checked equalities, and the potentials are the
numbers whose rows are checked.
-/

namespace QECComp

/-- One character of the record parser with key width `kw` and potential width `hw`. -/
def stepPW (kw hw : Nat) (st : PState) (c : Char) : PState :=
  let v := hexVal c
  if st.pos < kw then { st with pos := st.pos + 1, k := st.k * 16 + v }
  else if st.pos + 1 < kw + hw then { st with pos := st.pos + 1, h := st.h * 16 + v }
  else { pos := 0, k := 0, h := 0, keys := st.keys.push st.k, hs := st.hs.push (st.h * 16 + v) }

/-- The arrays of keys and potentials of the records in the chunks. -/
def loadDataW (kw hw : Nat) (chunks : List String) : Array Nat × Array Nat :=
  let st := chunks.foldl (fun st s => s.foldl (stepPW kw hw) st) ⟨0, 0, 0, #[], #[]⟩
  (st.keys, st.hs)

end QECComp
