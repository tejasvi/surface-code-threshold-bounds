import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 123231389..123722350 of seam certificate T10. -/
theorem near251 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 123231389 123722351 = true := by
  native_decide

end QECChecks.T10
