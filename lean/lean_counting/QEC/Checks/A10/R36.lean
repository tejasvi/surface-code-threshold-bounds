import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2184233..2244905 of certificate A10. -/
theorem rows36 : rowsOK PA10 keysA10 HsA10 2184233 2244906 = true := by
  native_decide

end QECChecks.A10
