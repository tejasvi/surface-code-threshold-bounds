import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 73633308..74134214 of augmented certificate R10. -/
theorem near147 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 73633308 74134215 = true := by
  native_decide

end QECChecks.R10
