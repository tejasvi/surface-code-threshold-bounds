import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- The start bound from the offsets 13..14, seam certificate T10. -/
theorem start22 : rangeAllT (13) 2 (startOKT PT10 nkT10 nGT10 bkT10 bHT10) = true := by
  native_decide

end QECChecks.T10
