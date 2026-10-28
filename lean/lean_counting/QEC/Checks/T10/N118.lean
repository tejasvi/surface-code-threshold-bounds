import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 57933482..58424442 of seam certificate T10. -/
theorem near118 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 57933482 58424443 = true := by
  native_decide

end QECChecks.T10
