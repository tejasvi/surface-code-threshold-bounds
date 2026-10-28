import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 3005441..3506347 of augmented certificate R10. -/
theorem near6 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 3005441 3506348 = true := by
  native_decide

end QECChecks.R10
