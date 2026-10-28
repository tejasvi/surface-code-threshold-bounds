import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 23542622..24043528 of augmented certificate R10. -/
theorem near47 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 23542622 24043529 = true := by
  native_decide

end QECChecks.R10
