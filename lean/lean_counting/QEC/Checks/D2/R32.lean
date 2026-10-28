import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1754391..1809215 of certificate D2. -/
theorem rows32 : rowsOK PD2 keysD2 HsD2 1754391 1809216 = true := by
  native_decide

end QECChecks.D2
