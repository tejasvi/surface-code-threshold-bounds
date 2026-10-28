import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 36065293..36566199 of augmented certificate R10. -/
theorem near72 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 36065293 36566200 = true := by
  native_decide

end QECChecks.R10
