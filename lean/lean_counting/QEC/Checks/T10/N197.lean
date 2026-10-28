import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 96719457..97210418 of seam certificate T10. -/
theorem near197 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 96719457 97210419 = true := by
  native_decide

end QECChecks.T10
