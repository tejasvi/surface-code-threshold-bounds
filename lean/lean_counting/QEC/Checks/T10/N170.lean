import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 83463491..83954451 of seam certificate T10. -/
theorem near170 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 83463491 83954452 = true := by
  native_decide

end QECChecks.T10
