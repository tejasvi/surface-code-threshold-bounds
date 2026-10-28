import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3563607..3618431 of certificate D2. -/
theorem rows65 : rowsOK PD2 keysD2 HsD2 3563607 3618432 = true := by
  native_decide

end QECChecks.D2
