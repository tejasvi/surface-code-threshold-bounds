import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 49088872..49589778 of augmented certificate R10. -/
theorem near98 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 49088872 49589779 = true := by
  native_decide

end QECChecks.R10
