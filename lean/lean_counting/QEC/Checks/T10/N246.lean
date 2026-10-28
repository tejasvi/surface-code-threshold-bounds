import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 120776581..121267541 of seam certificate T10. -/
theorem near246 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 120776581 121267542 = true := by
  native_decide

end QECChecks.T10
