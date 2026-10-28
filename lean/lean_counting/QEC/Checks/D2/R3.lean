import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 164474..219297 of certificate D2. -/
theorem rows3 : rowsOK PD2 keysD2 HsD2 164474 219298 = true := by
  native_decide

end QECChecks.D2
