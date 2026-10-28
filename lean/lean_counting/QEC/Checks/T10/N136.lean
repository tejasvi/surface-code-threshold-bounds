import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 66770792..67261753 of seam certificate T10. -/
theorem near136 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 66770792 67261754 = true := by
  native_decide

end QECChecks.T10
