import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 63615171..64116077 of augmented certificate R10. -/
theorem near127 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 63615171 64116078 = true := by
  native_decide

end QECChecks.R10
