import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 13524485..14025391 of augmented certificate R10. -/
theorem near27 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 13524485 14025392 = true := by
  native_decide

end QECChecks.R10
