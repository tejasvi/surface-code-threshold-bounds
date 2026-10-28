import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4331153..4385977 of certificate D2. -/
theorem rows79 : rowsOK PD2 keysD2 HsD2 4331153 4385978 = true := by
  native_decide

end QECChecks.D2
