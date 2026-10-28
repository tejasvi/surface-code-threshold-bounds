import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 35564387..36065292 of augmented certificate R10. -/
theorem near71 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 35564387 36065293 = true := by
  native_decide

end QECChecks.R10
