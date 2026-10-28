import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 12021764..12522670 of augmented certificate R10. -/
theorem near24 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 12021764 12522671 = true := by
  native_decide

end QECChecks.R10
