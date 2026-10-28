import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 67121519..67622425 of augmented certificate R10. -/
theorem near134 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 67121519 67622426 = true := by
  native_decide

end QECChecks.R10
