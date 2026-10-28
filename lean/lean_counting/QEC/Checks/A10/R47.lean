import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2851638..2912310 of certificate A10. -/
theorem rows47 : rowsOK PA10 keysA10 HsA10 2851638 2912311 = true := by
  native_decide

end QECChecks.A10
