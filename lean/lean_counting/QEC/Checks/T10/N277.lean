import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 135996394..136487355 of seam certificate T10. -/
theorem near277 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 135996394 136487356 = true := by
  native_decide

end QECChecks.T10
