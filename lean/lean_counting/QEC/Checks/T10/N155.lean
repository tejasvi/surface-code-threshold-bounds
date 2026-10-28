import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 76099065..76590026 of seam certificate T10. -/
theorem near155 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 76099065 76590027 = true := by
  native_decide

end QECChecks.T10
