import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 21602315..22093276 of seam certificate T10. -/
theorem near44 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 21602315 22093277 = true := by
  native_decide

end QECChecks.T10
