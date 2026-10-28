import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2790965..2851637 of certificate A10. -/
theorem rows46 : rowsOK PA10 keysA10 HsA10 2790965 2851638 = true := by
  native_decide

end QECChecks.A10
