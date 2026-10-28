import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 3215677..3276349 of certificate A10. -/
theorem rows53 : rowsOK PA10 keysA10 HsA10 3215677 3276350 = true := by
  native_decide

end QECChecks.A10
