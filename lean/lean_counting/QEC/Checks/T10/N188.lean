import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 92300801..92791762 of seam certificate T10. -/
theorem near188 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 92300801 92791763 = true := by
  native_decide

end QECChecks.T10
