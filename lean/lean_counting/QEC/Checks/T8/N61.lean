import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3876851..3940405 of seam certificate T8. -/
theorem near61 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3876851 3940406 = true := by
  native_decide

end QECChecks.T8
