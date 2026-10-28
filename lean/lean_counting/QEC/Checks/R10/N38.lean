import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 19034460..19535366 of augmented certificate R10. -/
theorem near38 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 19034460 19535367 = true := by
  native_decide

end QECChecks.R10
