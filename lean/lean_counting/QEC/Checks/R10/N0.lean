import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 0..500905 of augmented certificate R10. -/
theorem near0 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 0 500906 = true := by
  native_decide

end QECChecks.R10
