import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 135505432..135996393 of seam certificate T10. -/
theorem near276 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 135505432 135996394 = true := by
  native_decide

end QECChecks.T10
