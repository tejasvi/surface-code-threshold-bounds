import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 100156189..100647150 of seam certificate T10. -/
theorem near204 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 100156189 100647151 = true := by
  native_decide

end QECChecks.T10
