import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 1880867..1941540 of certificate A10. -/
theorem rows31 : rowsOK PA10 keysA10 HsA10 1880867 1941541 = true := by
  native_decide

end QECChecks.A10
