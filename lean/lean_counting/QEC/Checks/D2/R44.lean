import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2412288..2467111 of certificate D2. -/
theorem rows44 : rowsOK PD2 keysD2 HsD2 2412288 2467112 = true := by
  native_decide

end QECChecks.D2
