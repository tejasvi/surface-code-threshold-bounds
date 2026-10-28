import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 140415049..140906010 of seam certificate T10. -/
theorem near286 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 140415049 140906011 = true := by
  native_decide

end QECChecks.T10
