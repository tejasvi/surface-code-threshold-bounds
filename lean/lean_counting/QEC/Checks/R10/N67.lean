import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 33560759..34061665 of augmented certificate R10. -/
theorem near67 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 33560759 34061666 = true := by
  native_decide

end QECChecks.R10
