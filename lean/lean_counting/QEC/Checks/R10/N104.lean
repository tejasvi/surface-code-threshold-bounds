import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 52094313..52595219 of augmented certificate R10. -/
theorem near104 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 52094313 52595220 = true := by
  native_decide

end QECChecks.R10
