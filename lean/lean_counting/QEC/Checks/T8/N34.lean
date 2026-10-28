import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 2160868..2224422 of seam certificate T8. -/
theorem near34 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 2160868 2224423 = true := by
  native_decide

end QECChecks.T8
