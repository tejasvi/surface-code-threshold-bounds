import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 154652939..155143900 of seam certificate T10. -/
theorem near315 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 154652939 155143901 = true := by
  native_decide

end QECChecks.T10
