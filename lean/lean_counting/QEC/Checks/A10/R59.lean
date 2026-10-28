import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 3579716..3640388 of certificate A10. -/
theorem rows59 : rowsOK PA10 keysA10 HsA10 3579716 3640389 = true := by
  native_decide

end QECChecks.A10
