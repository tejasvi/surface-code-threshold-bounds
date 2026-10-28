import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 9517230..10018136 of augmented certificate R10. -/
theorem near19 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 9517230 10018137 = true := by
  native_decide

end QECChecks.R10
