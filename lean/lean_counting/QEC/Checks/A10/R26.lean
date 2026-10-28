import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 1577502..1638174 of certificate A10. -/
theorem rows26 : rowsOK PA10 keysA10 HsA10 1577502 1638175 = true := by
  native_decide

end QECChecks.A10
