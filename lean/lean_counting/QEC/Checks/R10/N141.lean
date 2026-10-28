import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 70627867..71128773 of augmented certificate R10. -/
theorem near141 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 70627867 71128774 = true := by
  native_decide

end QECChecks.R10
