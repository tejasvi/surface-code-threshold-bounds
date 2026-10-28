import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2467112..2521936 of certificate D2. -/
theorem rows45 : rowsOK PD2 keysD2 HsD2 2467112 2521937 = true := by
  native_decide

end QECChecks.D2
