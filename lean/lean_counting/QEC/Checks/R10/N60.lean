import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 30054411..30555317 of augmented certificate R10. -/
theorem near60 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 30054411 30555318 = true := by
  native_decide

end QECChecks.R10
