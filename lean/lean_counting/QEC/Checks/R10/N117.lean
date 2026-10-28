import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 58606102..59107008 of augmented certificate R10. -/
theorem near117 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 58606102 59107009 = true := by
  native_decide

end QECChecks.R10
