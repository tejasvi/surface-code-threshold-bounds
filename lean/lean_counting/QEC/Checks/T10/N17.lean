import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 8346349..8837309 of seam certificate T10. -/
theorem near17 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 8346349 8837310 = true := by
  native_decide

end QECChecks.T10
