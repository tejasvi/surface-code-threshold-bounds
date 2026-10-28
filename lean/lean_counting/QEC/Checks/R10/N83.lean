import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 41575269..42076175 of augmented certificate R10. -/
theorem near83 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 41575269 42076176 = true := by
  native_decide

end QECChecks.R10
