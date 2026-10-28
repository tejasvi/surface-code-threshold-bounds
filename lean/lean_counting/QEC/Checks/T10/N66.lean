import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 32403473..32894433 of seam certificate T10. -/
theorem near66 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 32403473 32894434 = true := by
  native_decide

end QECChecks.T10
