import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 56460596..56951557 of seam certificate T10. -/
theorem near115 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 56460596 56951558 = true := by
  native_decide

end QECChecks.T10
