import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 11019950..11520856 of augmented certificate R10. -/
theorem near22 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 11019950 11520857 = true := by
  native_decide

end QECChecks.R10
