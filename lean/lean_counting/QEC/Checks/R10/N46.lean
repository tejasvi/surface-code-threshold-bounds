import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 23041715..23542621 of augmented certificate R10. -/
theorem near46 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 23041715 23542622 = true := by
  native_decide

end QECChecks.R10
