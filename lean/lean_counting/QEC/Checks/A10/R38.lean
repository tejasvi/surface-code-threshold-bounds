import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2305579..2366252 of certificate A10. -/
theorem rows38 : rowsOK PA10 keysA10 HsA10 2305579 2366253 = true := by
  native_decide

end QECChecks.A10
