import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 53597033..54097939 of augmented certificate R10. -/
theorem near107 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 53597033 54097940 = true := by
  native_decide

end QECChecks.R10
