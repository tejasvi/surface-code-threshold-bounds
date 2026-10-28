import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 92791763..93282724 of seam certificate T10. -/
theorem near189 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 92791763 93282725 = true := by
  native_decide

end QECChecks.T10
