import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 75608103..76099064 of seam certificate T10. -/
theorem near154 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 75608103 76099065 = true := by
  native_decide

end QECChecks.T10
