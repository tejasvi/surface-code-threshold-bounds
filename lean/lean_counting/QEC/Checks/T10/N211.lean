import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 103592921..104083882 of seam certificate T10. -/
theorem near211 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 103592921 104083883 = true := by
  native_decide

end QECChecks.T10
