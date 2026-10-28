import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1206144..1260967 of certificate D2. -/
theorem rows22 : rowsOK PD2 keysD2 HsD2 1206144 1260968 = true := by
  native_decide

end QECChecks.D2
