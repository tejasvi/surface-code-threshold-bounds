import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 67752716..68243677 of seam certificate T10. -/
theorem near138 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 67752716 68243678 = true := by
  native_decide

end QECChecks.T10
