import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 107520615..108011575 of seam certificate T10. -/
theorem near219 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 107520615 108011576 = true := by
  native_decide

end QECChecks.T10
