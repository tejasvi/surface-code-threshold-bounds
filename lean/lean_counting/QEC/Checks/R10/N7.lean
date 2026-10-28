import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 3506348..4007253 of augmented certificate R10. -/
theorem near7 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 3506348 4007254 = true := by
  native_decide

end QECChecks.R10
