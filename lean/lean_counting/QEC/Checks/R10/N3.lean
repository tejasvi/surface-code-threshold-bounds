import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 1502720..2003626 of augmented certificate R10. -/
theorem near3 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 1502720 2003627 = true := by
  native_decide

end QECChecks.R10
