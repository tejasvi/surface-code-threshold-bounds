import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 970770..1031442 of certificate A10. -/
theorem rows16 : rowsOK PA10 keysA10 HsA10 970770 1031443 = true := by
  native_decide

end QECChecks.A10
