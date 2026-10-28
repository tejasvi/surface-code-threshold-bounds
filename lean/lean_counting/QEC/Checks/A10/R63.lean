import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 3822408..3883081 of certificate A10. -/
theorem rows63 : rowsOK PA10 keysA10 HsA10 3822408 3883082 = true := by
  native_decide

end QECChecks.A10
