import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 87391184..87882145 of seam certificate T10. -/
theorem near178 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 87391184 87882146 = true := by
  native_decide

end QECChecks.T10
