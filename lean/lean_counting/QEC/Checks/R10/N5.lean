import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 2504534..3005440 of augmented certificate R10. -/
theorem near5 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 2504534 3005441 = true := by
  native_decide

end QECChecks.R10
