import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 53096127..53597032 of augmented certificate R10. -/
theorem near106 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 53096127 53597033 = true := by
  native_decide

end QECChecks.R10
