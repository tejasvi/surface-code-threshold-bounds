import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 98192342..98683303 of seam certificate T10. -/
theorem near200 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 98192342 98683304 = true := by
  native_decide

end QECChecks.T10
