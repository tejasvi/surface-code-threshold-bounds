import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 728077..788750 of certificate A10. -/
theorem rows12 : rowsOK PA10 keysA10 HsA10 728077 788751 = true := by
  native_decide

end QECChecks.A10
