import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2669618..2730291 of certificate A10. -/
theorem rows44 : rowsOK PA10 keysA10 HsA10 2669618 2730292 = true := by
  native_decide

end QECChecks.A10
