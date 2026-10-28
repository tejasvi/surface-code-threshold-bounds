import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 60609730..61110635 of augmented certificate R10. -/
theorem near121 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 60609730 61110636 = true := by
  native_decide

end QECChecks.R10
