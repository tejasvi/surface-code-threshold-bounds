import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 485385..546057 of certificate A10. -/
theorem rows8 : rowsOK PA10 keysA10 HsA10 485385 546058 = true := by
  native_decide

end QECChecks.A10
