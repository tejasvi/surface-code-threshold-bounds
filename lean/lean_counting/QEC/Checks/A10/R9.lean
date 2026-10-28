import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 546058..606730 of certificate A10. -/
theorem rows9 : rowsOK PA10 keysA10 HsA10 546058 606731 = true := by
  native_decide

end QECChecks.A10
