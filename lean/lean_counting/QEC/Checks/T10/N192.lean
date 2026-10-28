import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 94264648..94755609 of seam certificate T10. -/
theorem near192 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 94264648 94755610 = true := by
  native_decide

end QECChecks.T10
