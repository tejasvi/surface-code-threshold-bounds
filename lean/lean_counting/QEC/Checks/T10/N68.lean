import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 33385396..33876357 of seam certificate T10. -/
theorem near68 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 33385396 33876358 = true := by
  native_decide

end QECChecks.T10
