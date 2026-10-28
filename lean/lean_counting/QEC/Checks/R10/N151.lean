import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 75636935..76137841 of augmented certificate R10. -/
theorem near151 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 75636935 76137842 = true := by
  native_decide

end QECChecks.R10
