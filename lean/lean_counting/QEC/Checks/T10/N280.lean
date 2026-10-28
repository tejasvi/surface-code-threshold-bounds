import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 137469279..137960240 of seam certificate T10. -/
theorem near280 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 137469279 137960241 = true := by
  native_decide

end QECChecks.T10
