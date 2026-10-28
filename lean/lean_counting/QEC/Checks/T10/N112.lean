import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 54987711..55478672 of seam certificate T10. -/
theorem near112 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 54987711 55478673 = true := by
  native_decide

end QECChecks.T10
