import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 2003627..2504533 of augmented certificate R10. -/
theorem near4 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 2003627 2504534 = true := by
  native_decide

end QECChecks.R10
