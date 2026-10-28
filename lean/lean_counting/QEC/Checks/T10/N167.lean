import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 81990605..82481566 of seam certificate T10. -/
theorem near167 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 81990605 82481567 = true := by
  native_decide

end QECChecks.T10
