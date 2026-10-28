import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 121346..182018 of certificate A10. -/
theorem rows2 : rowsOK PA10 keysA10 HsA10 121346 182019 = true := by
  native_decide

end QECChecks.A10
