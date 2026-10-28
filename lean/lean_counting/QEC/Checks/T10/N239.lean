import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 117339849..117830810 of seam certificate T10. -/
theorem near239 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 117339849 117830811 = true := by
  native_decide

end QECChecks.T10
