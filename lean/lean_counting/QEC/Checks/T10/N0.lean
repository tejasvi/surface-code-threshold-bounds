import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 0..490960 of seam certificate T10. -/
theorem near0 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 0 490961 = true := by
  native_decide

end QECChecks.T10
