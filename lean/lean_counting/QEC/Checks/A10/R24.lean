import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 1456155..1516827 of certificate A10. -/
theorem rows24 : rowsOK PA10 keysA10 HsA10 1456155 1516828 = true := by
  native_decide

end QECChecks.A10
