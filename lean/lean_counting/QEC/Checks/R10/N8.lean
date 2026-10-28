import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 4007254..4508160 of augmented certificate R10. -/
theorem near8 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 4007254 4508161 = true := by
  native_decide

end QECChecks.R10
