import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 51092499..51593405 of augmented certificate R10. -/
theorem near102 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 51092499 51593406 = true := by
  native_decide

end QECChecks.R10
