import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- The start bound from the offsets 13..22, seam certificate T8. -/
theorem start4 : rangeAllT (13) 10 (startOKT PT8 nkT8 nGT8 bkT8 bHT8) = true := by
  native_decide

end QECChecks.T8
