import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 139924088..140415048 of seam certificate T10. -/
theorem near285 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 139924088 140415049 = true := by
  native_decide

end QECChecks.T10
