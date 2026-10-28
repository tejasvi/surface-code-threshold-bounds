import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 8014509..8515415 of augmented certificate R10. -/
theorem near16 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 8014509 8515416 = true := by
  native_decide

end QECChecks.R10
