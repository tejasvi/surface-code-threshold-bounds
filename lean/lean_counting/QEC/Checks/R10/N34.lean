import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 17030833..17531739 of augmented certificate R10. -/
theorem near34 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 17030833 17531740 = true := by
  native_decide

end QECChecks.R10
