import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 4067516..4131070 of seam certificate T8. -/
theorem near64 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 4067516 4131071 = true := by
  native_decide

end QECChecks.T8
