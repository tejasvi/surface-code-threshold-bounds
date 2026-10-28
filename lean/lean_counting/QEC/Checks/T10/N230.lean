import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 112921193..113412154 of seam certificate T10. -/
theorem near230 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 112921193 113412155 = true := by
  native_decide

end QECChecks.T10
