import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3837731..3892554 of certificate D2. -/
theorem rows70 : rowsOK PD2 keysD2 HsD2 3837731 3892555 = true := by
  native_decide

end QECChecks.D2
