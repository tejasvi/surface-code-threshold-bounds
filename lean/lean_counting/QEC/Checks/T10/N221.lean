import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 108502538..108993499 of seam certificate T10. -/
theorem near221 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 108502538 108993500 = true := by
  native_decide

end QECChecks.T10
