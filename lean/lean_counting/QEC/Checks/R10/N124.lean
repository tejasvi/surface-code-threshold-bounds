import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 62112450..62613356 of augmented certificate R10. -/
theorem near124 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 62112450 62613357 = true := by
  native_decide

end QECChecks.R10
