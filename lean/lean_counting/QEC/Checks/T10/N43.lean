import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 21111353..21602314 of seam certificate T10. -/
theorem near43 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 21111353 21602315 = true := by
  native_decide

end QECChecks.T10
