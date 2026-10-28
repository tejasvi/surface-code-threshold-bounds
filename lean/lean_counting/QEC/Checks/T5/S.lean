import QECCountComp.Data.T5

namespace QECChecks.T5

open QECComp QECComp.Data

/-- The sizes of seam certificate T5. -/
theorem sizes : nkT5.size = 24392 ∧ nGT5.size = 24392 ∧ bkT5.size = 1220 ∧ bHT5.size = 1220 := by
  native_decide

/-- The start bound from the offset bigO, seam certificate T5. -/
theorem startBig : startOKT PT5 nkT5 nGT5 bkT5 bHT5 bigO = true := by
  native_decide

end QECChecks.T5
