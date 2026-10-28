import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- The sizes of seam certificate T8. -/
theorem sizes : nkT8.size = 5084396 ∧ nGT8.size = 5084396 ∧ bkT8.size = 159004 ∧ bHT8.size = 159004 := by
  native_decide

/-- The start bound from the offset bigO, seam certificate T8. -/
theorem startBig : startOKT PT8 nkT8 nGT8 bkT8 bHT8 bigO = true := by
  native_decide

end QECChecks.T8
