import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 82972529..83463490 of seam certificate T10. -/
theorem near169 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 82972529 83463491 = true := by
  native_decide

end QECChecks.T10
