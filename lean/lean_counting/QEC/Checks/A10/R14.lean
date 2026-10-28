import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 849424..910096 of certificate A10. -/
theorem rows14 : rowsOK PA10 keysA10 HsA10 849424 910097 = true := by
  native_decide

end QECChecks.A10
