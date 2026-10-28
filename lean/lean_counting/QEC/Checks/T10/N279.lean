import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 136978317..137469278 of seam certificate T10. -/
theorem near279 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 136978317 137469279 = true := by
  native_decide

end QECChecks.T10
