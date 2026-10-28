import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 31056225..31557131 of augmented certificate R10. -/
theorem near62 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 31056225 31557132 = true := by
  native_decide

end QECChecks.R10
