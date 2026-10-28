import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 1001813..1502719 of augmented certificate R10. -/
theorem near2 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 1001813 1502720 = true := by
  native_decide

end QECChecks.R10
