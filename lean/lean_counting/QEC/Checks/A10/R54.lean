import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 3276350..3337022 of certificate A10. -/
theorem rows54 : rowsOK PA10 keysA10 HsA10 3276350 3337023 = true := by
  native_decide

end QECChecks.A10
