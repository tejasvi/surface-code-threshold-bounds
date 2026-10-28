import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 37067107..37568013 of augmented certificate R10. -/
theorem near74 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 37067107 37568014 = true := by
  native_decide

end QECChecks.R10
