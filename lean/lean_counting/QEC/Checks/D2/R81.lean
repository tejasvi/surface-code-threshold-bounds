import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4440803..4495626 of certificate D2. -/
theorem rows81 : rowsOK PD2 keysD2 HsD2 4440803 4495627 = true := by
  native_decide

end QECChecks.D2
