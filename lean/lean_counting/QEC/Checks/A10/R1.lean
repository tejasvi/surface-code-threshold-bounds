import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 60673..121345 of certificate A10. -/
theorem rows1 : rowsOK PA10 keysA10 HsA10 60673 121346 = true := by
  native_decide

end QECChecks.A10
