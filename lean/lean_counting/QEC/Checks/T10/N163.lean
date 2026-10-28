import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 80026759..80517719 of seam certificate T10. -/
theorem near163 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 80026759 80517720 = true := by
  native_decide

end QECChecks.T10
