import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 54097940..54598846 of augmented certificate R10. -/
theorem near108 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 54097940 54598847 = true := by
  native_decide

end QECChecks.R10
