import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 46584337..47085243 of augmented certificate R10. -/
theorem near93 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 46584337 47085244 = true := by
  native_decide

end QECChecks.R10
