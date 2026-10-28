import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 80145097..80646003 of augmented certificate R10. -/
theorem near160 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 80145097 80646004 = true := by
  native_decide

end QECChecks.R10
