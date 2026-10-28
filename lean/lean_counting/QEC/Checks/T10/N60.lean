import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 29457702..29948663 of seam certificate T10. -/
theorem near60 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 29457702 29948664 = true := by
  native_decide

end QECChecks.T10
