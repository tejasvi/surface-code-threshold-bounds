import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 81146911..81647817 of augmented certificate R10. -/
theorem near162 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 81146911 81647818 = true := by
  native_decide

end QECChecks.R10
