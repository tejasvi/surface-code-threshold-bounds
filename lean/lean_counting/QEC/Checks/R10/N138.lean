import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 69125146..69626052 of augmented certificate R10. -/
theorem near138 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 69125146 69626053 = true := by
  native_decide

end QECChecks.R10
