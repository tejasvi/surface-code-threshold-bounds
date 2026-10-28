import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 155143901..155634861 of seam certificate T10. -/
theorem near316 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 155143901 155634862 = true := by
  native_decide

end QECChecks.T10
