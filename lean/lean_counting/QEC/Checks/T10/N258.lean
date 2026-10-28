import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 126668121..127159082 of seam certificate T10. -/
theorem near258 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 126668121 127159083 = true := by
  native_decide

end QECChecks.T10
