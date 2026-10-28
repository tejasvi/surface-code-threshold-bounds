import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 54598847..55099753 of augmented certificate R10. -/
theorem near109 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 54598847 55099754 = true := by
  native_decide

end QECChecks.R10
