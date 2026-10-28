import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 37804051..38295012 of seam certificate T10. -/
theorem near77 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 37804051 38295013 = true := by
  native_decide

end QECChecks.T10
