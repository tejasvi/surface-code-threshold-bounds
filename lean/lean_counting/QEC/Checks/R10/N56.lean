import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 28050784..28551690 of augmented certificate R10. -/
theorem near56 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 28050784 28551691 = true := by
  native_decide

end QECChecks.R10
