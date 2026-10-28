import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 16029019..16529925 of augmented certificate R10. -/
theorem near32 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 16029019 16529926 = true := by
  native_decide

end QECChecks.R10
