import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 43695592..44186553 of seam certificate T10. -/
theorem near89 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 43695592 44186554 = true := by
  native_decide

end QECChecks.T10
