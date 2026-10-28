import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 26020970..26511931 of seam certificate T10. -/
theorem near53 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 26020970 26511932 = true := by
  native_decide

end QECChecks.T10
