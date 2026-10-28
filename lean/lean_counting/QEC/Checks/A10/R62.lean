import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 3761735..3822407 of certificate A10. -/
theorem rows62 : rowsOK PA10 keysA10 HsA10 3761735 3822408 = true := by
  native_decide

end QECChecks.A10
