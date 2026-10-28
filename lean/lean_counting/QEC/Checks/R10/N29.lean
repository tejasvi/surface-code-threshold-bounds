import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 14526298..15027204 of augmented certificate R10. -/
theorem near29 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 14526298 15027205 = true := by
  native_decide

end QECChecks.R10
