import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 1274136..1334808 of certificate A10. -/
theorem rows21 : rowsOK PA10 keysA10 HsA10 1274136 1334809 = true := by
  native_decide

end QECChecks.A10
