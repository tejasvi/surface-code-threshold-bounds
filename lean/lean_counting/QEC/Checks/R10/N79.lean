import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 39571641..40072547 of augmented certificate R10. -/
theorem near79 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 39571641 40072548 = true := by
  native_decide

end QECChecks.R10
