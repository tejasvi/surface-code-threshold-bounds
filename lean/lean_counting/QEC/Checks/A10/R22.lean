import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 1334809..1395481 of certificate A10. -/
theorem rows22 : rowsOK PA10 keysA10 HsA10 1334809 1395482 = true := by
  native_decide

end QECChecks.A10
