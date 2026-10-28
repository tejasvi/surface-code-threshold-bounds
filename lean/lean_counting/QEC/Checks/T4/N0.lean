import QECCountComp.Data.T4

namespace QECChecks.T4

open QECComp QECComp.Data

/-- Rows of the near states 0..1919 of seam certificate T4. -/
theorem near0 : nearRowsOK PT4 nkT4 nGT4 bkT4 bHT4 0 1920 = true := by
  native_decide

end QECChecks.T4
