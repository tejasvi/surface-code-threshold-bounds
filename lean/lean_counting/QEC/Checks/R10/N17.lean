import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 8515416..9016322 of augmented certificate R10. -/
theorem near17 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 8515416 9016323 = true := by
  native_decide

end QECChecks.R10
