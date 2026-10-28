import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4769751..4824575 of certificate D2. -/
theorem rows87 : rowsOK PD2 keysD2 HsD2 4769751 4824576 = true := by
  native_decide

end QECChecks.D2
