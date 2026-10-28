import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 95246572..95737532 of seam certificate T10. -/
theorem near194 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 95246572 95737533 = true := by
  native_decide

end QECChecks.T10
