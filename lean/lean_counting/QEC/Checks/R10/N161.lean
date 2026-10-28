import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 80646004..81146910 of augmented certificate R10. -/
theorem near161 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 80646004 81146911 = true := by
  native_decide

end QECChecks.R10
