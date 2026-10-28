import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2487599..2548271 of certificate A10. -/
theorem rows41 : rowsOK PA10 keysA10 HsA10 2487599 2548272 = true := by
  native_decide

end QECChecks.A10
