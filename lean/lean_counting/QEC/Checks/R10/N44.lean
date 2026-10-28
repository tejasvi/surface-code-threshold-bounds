import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 22039901..22540807 of augmented certificate R10. -/
theorem near44 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 22039901 22540808 = true := by
  native_decide

end QECChecks.R10
