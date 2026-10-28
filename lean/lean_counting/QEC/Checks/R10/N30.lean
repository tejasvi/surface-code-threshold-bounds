import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 15027205..15528111 of augmented certificate R10. -/
theorem near30 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 15027205 15528112 = true := by
  native_decide

end QECChecks.R10
