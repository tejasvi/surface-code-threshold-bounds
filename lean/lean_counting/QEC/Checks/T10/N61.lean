import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 29948664..30439625 of seam certificate T10. -/
theorem near61 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 29948664 30439626 = true := by
  native_decide

end QECChecks.T10
