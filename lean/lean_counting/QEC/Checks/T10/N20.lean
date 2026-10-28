import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 9819234..10310194 of seam certificate T10. -/
theorem near20 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 9819234 10310195 = true := by
  native_decide

end QECChecks.T10
