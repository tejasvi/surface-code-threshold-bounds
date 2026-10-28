import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 61611543..62112449 of augmented certificate R10. -/
theorem near123 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 61611543 62112450 = true := by
  native_decide

end QECChecks.R10
