import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 3094330..3155003 of certificate A10. -/
theorem rows51 : rowsOK PA10 keysA10 HsA10 3094330 3155004 = true := by
  native_decide

end QECChecks.A10
