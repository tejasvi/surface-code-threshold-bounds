import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 14025392..14526297 of augmented certificate R10. -/
theorem near28 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 14025392 14526298 = true := by
  native_decide

end QECChecks.R10
