import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 303365..364037 of certificate A10. -/
theorem rows5 : rowsOK PA10 keysA10 HsA10 303365 364038 = true := by
  native_decide

end QECChecks.A10
