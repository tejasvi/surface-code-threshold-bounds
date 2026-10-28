import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 63825022..64315983 of seam certificate T10. -/
theorem near130 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 63825022 64315984 = true := by
  native_decide

end QECChecks.T10
