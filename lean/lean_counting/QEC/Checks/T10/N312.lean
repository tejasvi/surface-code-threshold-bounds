import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 153180054..153671015 of seam certificate T10. -/
theorem near312 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 153180054 153671016 = true := by
  native_decide

end QECChecks.T10
