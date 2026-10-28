import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 5400578..5891539 of seam certificate T10. -/
theorem near11 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 5400578 5891540 = true := by
  native_decide

end QECChecks.T10
