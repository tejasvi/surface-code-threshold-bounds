import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2357463..2412287 of certificate D2. -/
theorem rows43 : rowsOK PD2 keysD2 HsD2 2357463 2412288 = true := by
  native_decide

end QECChecks.D2
