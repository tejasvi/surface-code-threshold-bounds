import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 64116078..64616983 of augmented certificate R10. -/
theorem near128 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 64116078 64616984 = true := by
  native_decide

end QECChecks.R10
