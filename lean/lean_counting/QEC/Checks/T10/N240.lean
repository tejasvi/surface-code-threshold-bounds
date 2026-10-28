import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 117830811..118321771 of seam certificate T10. -/
theorem near240 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 117830811 118321772 = true := by
  native_decide

end QECChecks.T10
