import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 47132324..47623285 of seam certificate T10. -/
theorem near96 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 47132324 47623286 = true := by
  native_decide

end QECChecks.T10
