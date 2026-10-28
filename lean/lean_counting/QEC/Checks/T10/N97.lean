import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 47623286..48114246 of seam certificate T10. -/
theorem near97 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 47623286 48114247 = true := by
  native_decide

end QECChecks.T10
