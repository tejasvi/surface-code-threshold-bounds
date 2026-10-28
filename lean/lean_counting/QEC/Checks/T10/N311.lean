import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 152689092..153180053 of seam certificate T10. -/
theorem near311 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 152689092 153180054 = true := by
  native_decide

end QECChecks.T10
