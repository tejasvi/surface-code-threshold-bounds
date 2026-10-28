import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 42713668..43204629 of seam certificate T10. -/
theorem near87 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 42713668 43204630 = true := by
  native_decide

end QECChecks.T10
