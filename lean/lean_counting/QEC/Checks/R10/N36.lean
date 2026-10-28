import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 18032646..18533552 of augmented certificate R10. -/
theorem near36 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 18032646 18533553 = true := by
  native_decide

end QECChecks.R10
