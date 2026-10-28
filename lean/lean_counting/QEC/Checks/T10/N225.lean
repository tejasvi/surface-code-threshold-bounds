import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 110466385..110957346 of seam certificate T10. -/
theorem near225 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 110466385 110957347 = true := by
  native_decide

end QECChecks.T10
