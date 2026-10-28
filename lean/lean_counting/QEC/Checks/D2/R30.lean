import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1644741..1699565 of certificate D2. -/
theorem rows30 : rowsOK PD2 keysD2 HsD2 1644741 1699566 = true := by
  native_decide

end QECChecks.D2
