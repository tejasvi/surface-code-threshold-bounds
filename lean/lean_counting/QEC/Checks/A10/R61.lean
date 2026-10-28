import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 3701062..3761734 of certificate A10. -/
theorem rows61 : rowsOK PA10 keysA10 HsA10 3701062 3761735 = true := by
  native_decide

end QECChecks.A10
