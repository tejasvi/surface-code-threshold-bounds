import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 45081617..45582523 of augmented certificate R10. -/
theorem near90 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 45081617 45582524 = true := by
  native_decide

end QECChecks.R10
