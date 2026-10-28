import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 11520857..12021763 of augmented certificate R10. -/
theorem near23 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 11520857 12021764 = true := by
  native_decide

end QECChecks.R10
