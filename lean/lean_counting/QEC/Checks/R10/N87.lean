import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 43578896..44079802 of augmented certificate R10. -/
theorem near87 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 43578896 44079803 = true := by
  native_decide

end QECChecks.R10
