import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 77139656..77640562 of augmented certificate R10. -/
theorem near154 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 77139656 77640563 = true := by
  native_decide

end QECChecks.R10
