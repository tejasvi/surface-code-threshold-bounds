import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 25530009..26020969 of seam certificate T10. -/
theorem near52 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 25530009 26020970 = true := by
  native_decide

end QECChecks.T10
