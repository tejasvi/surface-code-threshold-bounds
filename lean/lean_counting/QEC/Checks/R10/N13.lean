import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 6511789..7012695 of augmented certificate R10. -/
theorem near13 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 6511789 7012696 = true := by
  native_decide

end QECChecks.R10
