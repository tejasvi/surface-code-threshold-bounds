import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 1698848..1759520 of certificate A10. -/
theorem rows28 : rowsOK PA10 keysA10 HsA10 1698848 1759521 = true := by
  native_decide

end QECChecks.A10
