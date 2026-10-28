import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 31421549..31912510 of seam certificate T10. -/
theorem near64 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 31421549 31912511 = true := by
  native_decide

end QECChecks.T10
