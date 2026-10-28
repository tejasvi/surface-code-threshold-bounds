import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 981923..1472884 of seam certificate T10. -/
theorem near2 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 981923 1472885 = true := by
  native_decide

end QECChecks.T10
