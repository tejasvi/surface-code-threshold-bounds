import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 114885040..115376001 of seam certificate T10. -/
theorem near234 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 114885040 115376002 = true := by
  native_decide

end QECChecks.T10
