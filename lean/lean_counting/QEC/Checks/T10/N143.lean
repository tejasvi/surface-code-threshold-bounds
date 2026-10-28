import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 70207524..70698485 of seam certificate T10. -/
theorem near143 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 70207524 70698486 = true := by
  native_decide

end QECChecks.T10
