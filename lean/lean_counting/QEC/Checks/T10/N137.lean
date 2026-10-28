import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 67261754..67752715 of seam certificate T10. -/
theorem near137 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 67261754 67752716 = true := by
  native_decide

end QECChecks.T10
