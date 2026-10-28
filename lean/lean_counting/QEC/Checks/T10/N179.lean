import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 87882146..88373107 of seam certificate T10. -/
theorem near179 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 87882146 88373108 = true := by
  native_decide

end QECChecks.T10
