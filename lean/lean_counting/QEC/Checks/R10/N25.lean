import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 12522671..13023577 of augmented certificate R10. -/
theorem near25 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 12522671 13023578 = true := by
  native_decide

end QECChecks.R10
