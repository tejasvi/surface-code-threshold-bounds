import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 3640389..3701061 of certificate A10. -/
theorem rows60 : rowsOK PA10 keysA10 HsA10 3640389 3701062 = true := by
  native_decide

end QECChecks.A10
