import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 41074362..41575268 of augmented certificate R10. -/
theorem near82 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 41074362 41575269 = true := by
  native_decide

end QECChecks.R10
