import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 9016323..9517229 of augmented certificate R10. -/
theorem near18 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 9016323 9517230 = true := by
  native_decide

end QECChecks.R10
