import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 10519044..11019949 of augmented certificate R10. -/
theorem near21 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 10519044 11019950 = true := by
  native_decide

end QECChecks.R10
