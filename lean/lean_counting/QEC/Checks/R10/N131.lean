import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 65618798..66119704 of augmented certificate R10. -/
theorem near131 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 65618798 66119705 = true := by
  native_decide

end QECChecks.R10
