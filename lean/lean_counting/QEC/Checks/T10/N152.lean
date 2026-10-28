import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 74626180..75117141 of seam certificate T10. -/
theorem near152 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 74626180 75117142 = true := by
  native_decide

end QECChecks.T10
