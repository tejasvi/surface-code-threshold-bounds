import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 75117142..75608102 of seam certificate T10. -/
theorem near153 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 75117142 75608103 = true := by
  native_decide

end QECChecks.T10
