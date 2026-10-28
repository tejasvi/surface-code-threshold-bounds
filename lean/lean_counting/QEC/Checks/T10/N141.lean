import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 69225601..69716562 of seam certificate T10. -/
theorem near141 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 69225601 69716563 = true := by
  native_decide

end QECChecks.T10
