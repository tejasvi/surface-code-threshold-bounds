import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 182019..242691 of certificate A10. -/
theorem rows3 : rowsOK PA10 keysA10 HsA10 182019 242692 = true := by
  native_decide

end QECChecks.A10
