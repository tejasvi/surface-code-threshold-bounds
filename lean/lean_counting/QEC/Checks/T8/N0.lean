import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 0..63553 of seam certificate T8. -/
theorem near0 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 0 63554 = true := by
  native_decide

end QECChecks.T8
