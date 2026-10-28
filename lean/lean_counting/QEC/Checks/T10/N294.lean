import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 144342743..144833704 of seam certificate T10. -/
theorem near294 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 144342743 144833705 = true := by
  native_decide

end QECChecks.T10
