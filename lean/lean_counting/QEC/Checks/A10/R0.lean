import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 0..60672 of certificate A10. -/
theorem rows0 : rowsOK PA10 keysA10 HsA10 0 60673 = true := by
  native_decide

end QECChecks.A10
