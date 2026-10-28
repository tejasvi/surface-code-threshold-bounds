import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 1941541..2002213 of certificate A10. -/
theorem rows32 : rowsOK PA10 keysA10 HsA10 1941541 2002214 = true := by
  native_decide

end QECChecks.A10
