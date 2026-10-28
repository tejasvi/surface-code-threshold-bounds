import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 5020841..5084395 of seam certificate T8. -/
theorem near79 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 5020841 5084396 = true := by
  native_decide

end QECChecks.T8
