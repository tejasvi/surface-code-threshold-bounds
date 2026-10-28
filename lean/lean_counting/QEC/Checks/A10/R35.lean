import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2123560..2184232 of certificate A10. -/
theorem rows35 : rowsOK PA10 keysA10 HsA10 2123560 2184233 = true := by
  native_decide

end QECChecks.A10
