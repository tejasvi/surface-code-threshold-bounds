import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 1638175..1698847 of certificate A10. -/
theorem rows27 : rowsOK PA10 keysA10 HsA10 1638175 1698848 = true := by
  native_decide

end QECChecks.A10
