import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 122249466..122740427 of seam certificate T10. -/
theorem near249 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 122249466 122740428 = true := by
  native_decide

end QECChecks.T10
