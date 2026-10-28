import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 4508161..5009067 of augmented certificate R10. -/
theorem near9 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 4508161 5009068 = true := by
  native_decide

end QECChecks.R10
