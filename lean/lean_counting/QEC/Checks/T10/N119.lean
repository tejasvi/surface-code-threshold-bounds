import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 58424443..58915404 of seam certificate T10. -/
theorem near119 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 58424443 58915405 = true := by
  native_decide

end QECChecks.T10
