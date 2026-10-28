import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 97701380..98192341 of seam certificate T10. -/
theorem near199 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 97701380 98192342 = true := by
  native_decide

end QECChecks.T10
