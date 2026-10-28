import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 1398208..1461762 of seam certificate T8. -/
theorem near22 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 1398208 1461763 = true := by
  native_decide

end QECChecks.T8
