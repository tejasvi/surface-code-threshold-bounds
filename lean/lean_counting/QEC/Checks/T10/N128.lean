import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 62843099..63334059 of seam certificate T10. -/
theorem near128 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 62843099 63334060 = true := by
  native_decide

end QECChecks.T10
