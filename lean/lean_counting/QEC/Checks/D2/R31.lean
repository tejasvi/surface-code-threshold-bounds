import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1699566..1754390 of certificate D2. -/
theorem rows31 : rowsOK PD2 keysD2 HsD2 1699566 1754391 = true := by
  native_decide

end QECChecks.D2
