import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 34367319..34858280 of seam certificate T10. -/
theorem near70 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 34367319 34858281 = true := by
  native_decide

end QECChecks.T10
