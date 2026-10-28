import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 59897328..60388289 of seam certificate T10. -/
theorem near122 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 59897328 60388290 = true := by
  native_decide

end QECChecks.T10
