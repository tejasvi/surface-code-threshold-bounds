import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 6873463..7364424 of seam certificate T10. -/
theorem near14 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 6873463 7364425 = true := by
  native_decide

end QECChecks.T10
