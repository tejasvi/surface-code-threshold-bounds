import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 12765004..13255965 of seam certificate T10. -/
theorem near26 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 12765004 13255966 = true := by
  native_decide

end QECChecks.T10
