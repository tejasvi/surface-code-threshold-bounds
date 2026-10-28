import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 71128774..71629679 of augmented certificate R10. -/
theorem near142 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 71128774 71629680 = true := by
  native_decide

end QECChecks.R10
