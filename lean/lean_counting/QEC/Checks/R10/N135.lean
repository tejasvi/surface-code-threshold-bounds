import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 67622426..68123331 of augmented certificate R10. -/
theorem near135 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 67622426 68123332 = true := by
  native_decide

end QECChecks.R10
