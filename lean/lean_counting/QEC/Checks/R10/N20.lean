import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 10018137..10519043 of augmented certificate R10. -/
theorem near20 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 10018137 10519044 = true := by
  native_decide

end QECChecks.R10
