import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 29052597..29553503 of augmented certificate R10. -/
theorem near58 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 29052597 29553504 = true := by
  native_decide

end QECChecks.R10
