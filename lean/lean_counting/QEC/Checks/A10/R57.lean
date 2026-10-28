import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 3458369..3519042 of certificate A10. -/
theorem rows57 : rowsOK PA10 keysA10 HsA10 3458369 3519043 = true := by
  native_decide

end QECChecks.A10
