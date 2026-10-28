import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 108993500..109484460 of seam certificate T10. -/
theorem near222 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 108993500 109484461 = true := by
  native_decide

end QECChecks.T10
