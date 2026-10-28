import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 29553504..30054410 of augmented certificate R10. -/
theorem near59 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 29553504 30054411 = true := by
  native_decide

end QECChecks.R10
