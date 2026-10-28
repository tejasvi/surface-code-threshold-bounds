import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3782906..3837730 of certificate D2. -/
theorem rows69 : rowsOK PD2 keysD2 HsD2 3782906 3837731 = true := by
  native_decide

end QECChecks.D2
