import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 6010882..6511788 of augmented certificate R10. -/
theorem near12 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 6010882 6511789 = true := by
  native_decide

end QECChecks.R10
