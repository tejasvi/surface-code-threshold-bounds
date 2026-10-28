import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 7855387..8346348 of seam certificate T10. -/
theorem near16 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 7855387 8346349 = true := by
  native_decide

end QECChecks.T10
