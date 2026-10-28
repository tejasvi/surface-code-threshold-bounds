import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 121758504..122249465 of seam certificate T10. -/
theorem near248 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 121758504 122249466 = true := by
  native_decide

end QECChecks.T10
