import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 40072548..40573454 of augmented certificate R10. -/
theorem near80 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 40072548 40573455 = true := by
  native_decide

end QECChecks.R10
