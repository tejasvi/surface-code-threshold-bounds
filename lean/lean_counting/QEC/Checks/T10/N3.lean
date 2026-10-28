import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 1472885..1963845 of seam certificate T10. -/
theorem near3 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 1472885 1963846 = true := by
  native_decide

end QECChecks.T10
