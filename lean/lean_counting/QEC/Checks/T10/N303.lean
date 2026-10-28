import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 148761398..149252359 of seam certificate T10. -/
theorem near303 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 148761398 149252360 = true := by
  native_decide

end QECChecks.T10
