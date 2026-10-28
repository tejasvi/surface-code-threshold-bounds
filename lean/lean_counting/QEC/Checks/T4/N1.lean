import QECCountComp.Data.T4

namespace QECChecks.T4

open QECComp QECComp.Data

/-- Rows of the near states 1920..3839 of seam certificate T4. -/
theorem near1 : nearRowsOK PT4 nkT4 nGT4 bkT4 bHT4 1920 3840 = true := by
  native_decide

end QECChecks.T4
