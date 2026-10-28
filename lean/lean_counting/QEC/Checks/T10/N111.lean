import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 54496750..54987710 of seam certificate T10. -/
theorem near111 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 54496750 54987711 = true := by
  native_decide

end QECChecks.T10
