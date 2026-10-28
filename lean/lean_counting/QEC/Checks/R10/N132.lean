import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 66119705..66620611 of augmented certificate R10. -/
theorem near132 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 66119705 66620612 = true := by
  native_decide

end QECChecks.R10
