import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 11292119..11783080 of seam certificate T10. -/
theorem near23 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 11292119 11783081 = true := by
  native_decide

end QECChecks.T10
