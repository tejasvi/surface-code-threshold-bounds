import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3673256..3728080 of certificate D2. -/
theorem rows67 : rowsOK PD2 keysD2 HsD2 3673256 3728081 = true := by
  native_decide

end QECChecks.D2
