import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 88373108..88864068 of seam certificate T10. -/
theorem near180 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 88373108 88864069 = true := by
  native_decide

end QECChecks.T10
