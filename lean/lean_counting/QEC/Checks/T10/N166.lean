import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 81499644..81990604 of seam certificate T10. -/
theorem near166 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 81499644 81990605 = true := by
  native_decide

end QECChecks.T10
