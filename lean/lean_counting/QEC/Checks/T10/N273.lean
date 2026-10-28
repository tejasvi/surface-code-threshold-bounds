import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 134032547..134523508 of seam certificate T10. -/
theorem near273 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 134032547 134523509 = true := by
  native_decide

end QECChecks.T10
