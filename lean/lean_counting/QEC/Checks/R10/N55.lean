import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 27549877..28050783 of augmented certificate R10. -/
theorem near55 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 27549877 28050784 = true := by
  native_decide

end QECChecks.R10
