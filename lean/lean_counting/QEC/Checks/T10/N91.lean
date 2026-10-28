import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 44677515..45168476 of seam certificate T10. -/
theorem near91 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 44677515 45168477 = true := by
  native_decide

end QECChecks.T10
