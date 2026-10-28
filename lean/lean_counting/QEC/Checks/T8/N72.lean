import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 4575956..4639510 of seam certificate T8. -/
theorem near72 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 4575956 4639511 = true := by
  native_decide

end QECChecks.T8
