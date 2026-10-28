import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 133050624..133541584 of seam certificate T10. -/
theorem near271 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 133050624 133541585 = true := by
  native_decide

end QECChecks.T10
