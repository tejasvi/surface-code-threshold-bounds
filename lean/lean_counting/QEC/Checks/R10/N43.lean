import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 21538994..22039900 of augmented certificate R10. -/
theorem near43 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 21538994 22039901 = true := by
  native_decide

end QECChecks.R10
