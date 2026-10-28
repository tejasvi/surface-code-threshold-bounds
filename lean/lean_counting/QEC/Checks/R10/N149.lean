import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 74635122..75136027 of augmented certificate R10. -/
theorem near149 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 74635122 75136028 = true := by
  native_decide

end QECChecks.R10
