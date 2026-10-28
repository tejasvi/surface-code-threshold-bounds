import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 30555318..31056224 of augmented certificate R10. -/
theorem near61 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 30555318 31056225 = true := by
  native_decide

end QECChecks.R10
