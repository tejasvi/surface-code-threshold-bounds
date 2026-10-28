import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 148270437..148761397 of seam certificate T10. -/
theorem near302 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 148270437 148761398 = true := by
  native_decide

end QECChecks.T10
