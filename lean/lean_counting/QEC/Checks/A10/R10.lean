import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 606731..667403 of certificate A10. -/
theorem rows10 : rowsOK PA10 keysA10 HsA10 606731 667404 = true := by
  native_decide

end QECChecks.A10
