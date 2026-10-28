import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 57103382..57604287 of augmented certificate R10. -/
theorem near114 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 57103382 57604288 = true := by
  native_decide

end QECChecks.R10
