import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 72171371..72662332 of seam certificate T10. -/
theorem near147 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 72171371 72662333 = true := by
  native_decide

end QECChecks.T10
