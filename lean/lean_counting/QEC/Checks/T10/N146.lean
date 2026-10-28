import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 71680410..72171370 of seam certificate T10. -/
theorem near146 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 71680410 72171371 = true := by
  native_decide

end QECChecks.T10
