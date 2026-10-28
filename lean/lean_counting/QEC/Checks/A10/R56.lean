import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 3397696..3458368 of certificate A10. -/
theorem rows56 : rowsOK PA10 keysA10 HsA10 3397696 3458369 = true := by
  native_decide

end QECChecks.A10
