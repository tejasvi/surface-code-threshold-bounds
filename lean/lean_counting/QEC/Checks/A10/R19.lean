import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 1152789..1213462 of certificate A10. -/
theorem rows19 : rowsOK PA10 keysA10 HsA10 1152789 1213463 = true := by
  native_decide

end QECChecks.A10
