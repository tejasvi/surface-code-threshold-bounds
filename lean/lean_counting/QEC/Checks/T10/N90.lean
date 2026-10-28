import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 44186554..44677514 of seam certificate T10. -/
theorem near90 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 44186554 44677515 = true := by
  native_decide

end QECChecks.T10
