import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 152198130..152689091 of seam certificate T10. -/
theorem near310 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 152198130 152689092 = true := by
  native_decide

end QECChecks.T10
