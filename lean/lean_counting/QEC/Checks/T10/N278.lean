import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 136487356..136978316 of seam certificate T10. -/
theorem near278 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 136487356 136978317 = true := by
  native_decide

end QECChecks.T10
