import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 1588873..1652427 of seam certificate T8. -/
theorem near25 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 1588873 1652428 = true := by
  native_decide

end QECChecks.T8
