import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 7513602..8014508 of augmented certificate R10. -/
theorem near15 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 7513602 8014509 = true := by
  native_decide

end QECChecks.R10
