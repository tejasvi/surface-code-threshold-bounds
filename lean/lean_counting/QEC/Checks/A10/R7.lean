import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 424712..485384 of certificate A10. -/
theorem rows7 : rowsOK PA10 keysA10 HsA10 424712 485385 = true := by
  native_decide

end QECChecks.A10
