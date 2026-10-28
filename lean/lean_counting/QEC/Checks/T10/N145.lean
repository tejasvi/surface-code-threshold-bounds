import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 71189448..71680409 of seam certificate T10. -/
theorem near145 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 71189448 71680410 = true := by
  native_decide

end QECChecks.T10
