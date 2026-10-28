import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 493422..548246 of certificate D2. -/
theorem rows9 : rowsOK PD2 keysD2 HsD2 493422 548247 = true := by
  native_decide

end QECChecks.D2
