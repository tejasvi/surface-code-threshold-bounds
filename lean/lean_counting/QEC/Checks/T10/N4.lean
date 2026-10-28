import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 1963846..2454807 of seam certificate T10. -/
theorem near4 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 1963846 2454808 = true := by
  native_decide

end QECChecks.T10
