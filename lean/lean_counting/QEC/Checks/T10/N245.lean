import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 120285619..120776580 of seam certificate T10. -/
theorem near245 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 120285619 120776581 = true := by
  native_decide

end QECChecks.T10
