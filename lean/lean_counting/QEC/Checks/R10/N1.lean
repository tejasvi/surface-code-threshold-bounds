import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 500906..1001812 of augmented certificate R10. -/
theorem near1 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 500906 1001813 = true := by
  native_decide

end QECChecks.R10
