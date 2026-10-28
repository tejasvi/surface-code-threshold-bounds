import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 86900223..87391183 of seam certificate T10. -/
theorem near177 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 86900223 87391184 = true := by
  native_decide

end QECChecks.T10
