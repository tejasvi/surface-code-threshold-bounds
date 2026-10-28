import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2548272..2608944 of certificate A10. -/
theorem rows42 : rowsOK PA10 keysA10 HsA10 2548272 2608945 = true := by
  native_decide

end QECChecks.A10
