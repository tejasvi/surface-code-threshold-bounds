import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 25546249..26047155 of augmented certificate R10. -/
theorem near51 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 25546249 26047156 = true := by
  native_decide

end QECChecks.R10
