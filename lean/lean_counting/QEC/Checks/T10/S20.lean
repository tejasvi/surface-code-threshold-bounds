import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- The start bound from the offsets 9..10, seam certificate T10. -/
theorem start20 : rangeAllT (9) 2 (startOKT PT10 nkT10 nGT10 bkT10 bHT10) = true := by
  native_decide

end QECChecks.T10
