import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2426926..2487598 of certificate A10. -/
theorem rows40 : rowsOK PA10 keysA10 HsA10 2426926 2487599 = true := by
  native_decide

end QECChecks.A10
