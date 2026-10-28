import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 28966741..29457701 of seam certificate T10. -/
theorem near59 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 28966741 29457702 = true := by
  native_decide

end QECChecks.T10
