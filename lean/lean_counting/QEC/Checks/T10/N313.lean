import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 153671016..154161976 of seam certificate T10. -/
theorem near313 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 153671016 154161977 = true := by
  native_decide

end QECChecks.T10
