import QECCountComp.Data.T5

namespace QECChecks.T5

open QECComp QECComp.Data

/-- The start bound from the offsets -14..13, seam certificate T5. -/
theorem start1 : rangeAllT (-14) 28 (startOKT PT5 nkT5 nGT5 bkT5 bHT5) = true := by
  native_decide

end QECChecks.T5
