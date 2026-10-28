import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 1395482..1456154 of certificate A10. -/
theorem rows23 : rowsOK PA10 keysA10 HsA10 1395482 1456155 = true := by
  native_decide

end QECChecks.A10
