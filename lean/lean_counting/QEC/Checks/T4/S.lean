import QECCountComp.Data.T4

namespace QECChecks.T4

open QECComp QECComp.Data

/-- The sizes of seam certificate T4. -/
theorem sizes : nkT4.size = 3840 ∧ nGT4.size = 3840 ∧ bkT4.size = 240 ∧ bHT4.size = 240 := by
  native_decide

/-- The start bound from the offset bigO, seam certificate T4. -/
theorem startBig : startOKT PT4 nkT4 nGT4 bkT4 bHT4 bigO = true := by
  native_decide

end QECChecks.T4
