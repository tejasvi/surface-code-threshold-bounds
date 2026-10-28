import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 135014470..135505431 of seam certificate T10. -/
theorem near275 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 135014470 135505432 = true := by
  native_decide

end QECChecks.T10
