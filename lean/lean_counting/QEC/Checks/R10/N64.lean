import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 32058039..32558944 of augmented certificate R10. -/
theorem near64 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 32058039 32558945 = true := by
  native_decide

end QECChecks.R10
