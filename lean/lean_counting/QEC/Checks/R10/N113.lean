import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 56602475..57103381 of augmented certificate R10. -/
theorem near113 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 56602475 57103382 = true := by
  native_decide

end QECChecks.R10
