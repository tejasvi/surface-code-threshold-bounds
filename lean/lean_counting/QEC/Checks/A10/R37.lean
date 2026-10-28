import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2244906..2305578 of certificate A10. -/
theorem rows37 : rowsOK PA10 keysA10 HsA10 2244906 2305579 = true := by
  native_decide

end QECChecks.A10
