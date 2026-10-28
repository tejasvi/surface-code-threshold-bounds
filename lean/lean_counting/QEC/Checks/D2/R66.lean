import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3618432..3673255 of certificate D2. -/
theorem rows66 : rowsOK PD2 keysD2 HsD2 3618432 3673256 = true := by
  native_decide

end QECChecks.D2
