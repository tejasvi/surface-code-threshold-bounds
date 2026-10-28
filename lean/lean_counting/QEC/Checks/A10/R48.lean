import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2912311..2972983 of certificate A10. -/
theorem rows48 : rowsOK PA10 keysA10 HsA10 2912311 2972984 = true := by
  native_decide

end QECChecks.A10
