import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 75136028..75636934 of augmented certificate R10. -/
theorem near150 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 75136028 75636935 = true := by
  native_decide

end QECChecks.R10
