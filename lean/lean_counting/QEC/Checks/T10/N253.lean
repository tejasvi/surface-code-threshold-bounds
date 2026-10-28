import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 124213313..124704273 of seam certificate T10. -/
theorem near253 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 124213313 124704274 = true := by
  native_decide

end QECChecks.T10
