import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 58915405..59406366 of seam certificate T10. -/
theorem near120 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 58915405 59406367 = true := by
  native_decide

end QECChecks.T10
