import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 133541585..134032546 of seam certificate T10. -/
theorem near272 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 133541585 134032547 = true := by
  native_decide

end QECChecks.T10
