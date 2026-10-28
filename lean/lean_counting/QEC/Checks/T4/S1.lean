import QECCountComp.Data.T4

namespace QECChecks.T4

open QECComp QECComp.Data

/-- The start bound from the offsets -11..10, seam certificate T4. -/
theorem start1 : rangeAllT (-11) 22 (startOKT PT4 nkT4 nGT4 bkT4 bHT4) = true := by
  native_decide

end QECChecks.T4
