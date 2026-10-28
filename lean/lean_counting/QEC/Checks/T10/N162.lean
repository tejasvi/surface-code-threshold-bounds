import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 79535797..80026758 of seam certificate T10. -/
theorem near162 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 79535797 80026759 = true := by
  native_decide

end QECChecks.T10
