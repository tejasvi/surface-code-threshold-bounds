import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 438597..493421 of certificate D2. -/
theorem rows8 : rowsOK PD2 keysD2 HsD2 438597 493422 = true := by
  native_decide

end QECChecks.D2
