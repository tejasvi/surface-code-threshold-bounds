import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2062887..2123559 of certificate A10. -/
theorem rows34 : rowsOK PA10 keysA10 HsA10 2062887 2123560 = true := by
  native_decide

end QECChecks.A10
