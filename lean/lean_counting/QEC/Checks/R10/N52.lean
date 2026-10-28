import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 26047156..26548062 of augmented certificate R10. -/
theorem near52 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 26047156 26548063 = true := by
  native_decide

end QECChecks.R10
