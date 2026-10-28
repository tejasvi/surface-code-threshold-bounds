import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 68123332..68624238 of augmented certificate R10. -/
theorem near136 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 68123332 68624239 = true := by
  native_decide

end QECChecks.R10
