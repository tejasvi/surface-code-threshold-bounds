import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 59406367..59897327 of seam certificate T10. -/
theorem near121 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 59406367 59897328 = true := by
  native_decide

end QECChecks.T10
