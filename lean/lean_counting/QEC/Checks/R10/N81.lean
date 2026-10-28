import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 40573455..41074361 of augmented certificate R10. -/
theorem near81 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 40573455 41074362 = true := by
  native_decide

end QECChecks.R10
