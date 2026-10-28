import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 6382502..6873462 of seam certificate T10. -/
theorem near13 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 6382502 6873463 = true := by
  native_decide

end QECChecks.T10
