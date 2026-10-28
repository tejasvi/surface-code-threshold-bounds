import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- The sizes of seam certificate T10. -/
theorem sizes : nkT10.size = 157107748 ∧ nGT10.size = 157107748 ∧ bkT10.size = 3930982 ∧ bHT10.size = 3930982 := by
  native_decide

/-- The start bound from the offset bigO, seam certificate T10. -/
theorem startBig : startOKT PT10 nkT10 nGT10 bkT10 bHT10 bigO = true := by
  native_decide

end QECChecks.T10
