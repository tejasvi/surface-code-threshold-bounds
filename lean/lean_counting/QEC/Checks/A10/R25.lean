import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 1516828..1577501 of certificate A10. -/
theorem rows25 : rowsOK PA10 keysA10 HsA10 1516828 1577502 = true := by
  native_decide

end QECChecks.A10
