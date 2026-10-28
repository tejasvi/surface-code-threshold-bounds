import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 108011576..108502537 of seam certificate T10. -/
theorem near220 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 108011576 108502538 = true := by
  native_decide

end QECChecks.T10
