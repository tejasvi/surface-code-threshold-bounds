import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 22540808..23041714 of augmented certificate R10. -/
theorem near45 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 22540808 23041715 = true := by
  native_decide

end QECChecks.R10
