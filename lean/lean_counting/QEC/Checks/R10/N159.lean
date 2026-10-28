import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 79644190..80145096 of augmented certificate R10. -/
theorem near159 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 79644190 80145097 = true := by
  native_decide

end QECChecks.R10
