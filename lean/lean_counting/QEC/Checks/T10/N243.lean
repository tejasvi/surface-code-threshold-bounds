import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 119303696..119794656 of seam certificate T10. -/
theorem near243 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 119303696 119794657 = true := by
  native_decide

end QECChecks.T10
