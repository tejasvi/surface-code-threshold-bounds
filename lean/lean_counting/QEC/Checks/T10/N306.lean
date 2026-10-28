import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 150234284..150725244 of seam certificate T10. -/
theorem near306 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 150234284 150725245 = true := by
  native_decide

end QECChecks.T10
