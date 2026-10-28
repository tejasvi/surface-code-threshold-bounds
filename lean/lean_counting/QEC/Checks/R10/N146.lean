import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 73132401..73633307 of augmented certificate R10. -/
theorem near146 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 73132401 73633308 = true := by
  native_decide

end QECChecks.R10
