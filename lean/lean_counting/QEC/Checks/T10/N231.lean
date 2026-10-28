import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 113412155..113903116 of seam certificate T10. -/
theorem near231 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 113412155 113903117 = true := by
  native_decide

end QECChecks.T10
