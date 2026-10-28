import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 54005788..54496749 of seam certificate T10. -/
theorem near110 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 54005788 54496750 = true := by
  native_decide

end QECChecks.T10
