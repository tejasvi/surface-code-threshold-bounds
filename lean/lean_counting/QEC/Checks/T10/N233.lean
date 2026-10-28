import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 114394079..114885039 of seam certificate T10. -/
theorem near233 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 114394079 114885040 = true := by
  native_decide

end QECChecks.T10
