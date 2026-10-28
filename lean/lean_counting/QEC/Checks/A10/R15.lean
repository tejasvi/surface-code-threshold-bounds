import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 910097..970769 of certificate A10. -/
theorem rows15 : rowsOK PA10 keysA10 HsA10 910097 970770 = true := by
  native_decide

end QECChecks.A10
