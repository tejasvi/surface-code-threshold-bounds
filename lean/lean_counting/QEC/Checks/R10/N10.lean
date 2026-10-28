import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 5009068..5509974 of augmented certificate R10. -/
theorem near10 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 5009068 5509975 = true := by
  native_decide

end QECChecks.R10
