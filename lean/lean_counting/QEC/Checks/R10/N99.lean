import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 49589779..50090684 of augmented certificate R10. -/
theorem near99 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 49589779 50090685 = true := by
  native_decide

end QECChecks.R10
