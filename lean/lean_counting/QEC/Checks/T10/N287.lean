import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 140906011..141396972 of seam certificate T10. -/
theorem near287 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 140906011 141396973 = true := by
  native_decide

end QECChecks.T10
