import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 130104853..130595814 of seam certificate T10. -/
theorem near265 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 130104853 130595815 = true := by
  native_decide

end QECChecks.T10
