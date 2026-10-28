import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 91809840..92300800 of seam certificate T10. -/
theorem near187 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 91809840 92300801 = true := by
  native_decide

end QECChecks.T10
