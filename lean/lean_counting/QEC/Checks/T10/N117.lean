import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 57442520..57933481 of seam certificate T10. -/
theorem near117 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 57442520 57933482 = true := by
  native_decide

end QECChecks.T10
