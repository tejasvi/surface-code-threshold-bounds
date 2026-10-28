import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- The start bound from the offsets 1..12, seam certificate T8. -/
theorem start3 : rangeAllT (1) 12 (startOKT PT8 nkT8 nGT8 bkT8 bHT8) = true := by
  native_decide

end QECChecks.T8
