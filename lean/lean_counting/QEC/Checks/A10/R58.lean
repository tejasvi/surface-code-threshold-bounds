import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 3519043..3579715 of certificate A10. -/
theorem rows58 : rowsOK PA10 keysA10 HsA10 3519043 3579716 = true := by
  native_decide

end QECChecks.A10
