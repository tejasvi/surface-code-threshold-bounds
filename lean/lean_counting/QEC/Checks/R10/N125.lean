import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 62613357..63114263 of augmented certificate R10. -/
theorem near125 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 62613357 63114264 = true := by
  native_decide

end QECChecks.R10
