import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 45659439..46150399 of seam certificate T10. -/
theorem near93 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 45659439 46150400 = true := by
  native_decide

end QECChecks.T10
