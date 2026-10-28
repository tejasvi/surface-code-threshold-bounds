import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 74134215..74635121 of augmented certificate R10. -/
theorem near148 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 74134215 74635122 = true := by
  native_decide

end QECChecks.R10
