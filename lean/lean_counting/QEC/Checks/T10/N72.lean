import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 35349243..35840204 of seam certificate T10. -/
theorem near72 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 35349243 35840205 = true := by
  native_decide

end QECChecks.T10
