import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 144833705..145324665 of seam certificate T10. -/
theorem near295 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 144833705 145324666 = true := by
  native_decide

end QECChecks.T10
