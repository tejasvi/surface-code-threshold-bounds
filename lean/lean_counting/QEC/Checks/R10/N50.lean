import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 25045342..25546248 of augmented certificate R10. -/
theorem near50 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 25045342 25546249 = true := by
  native_decide

end QECChecks.R10
