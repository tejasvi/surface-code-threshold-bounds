import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3728081..3782905 of certificate D2. -/
theorem rows68 : rowsOK PD2 keysD2 HsD2 3728081 3782906 = true := by
  native_decide

end QECChecks.D2
