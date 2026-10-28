import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 50090685..50591591 of augmented certificate R10. -/
theorem near100 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 50090685 50591592 = true := by
  native_decide

end QECChecks.R10
