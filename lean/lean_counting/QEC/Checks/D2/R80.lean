import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4385978..4440802 of certificate D2. -/
theorem rows80 : rowsOK PD2 keysD2 HsD2 4385978 4440803 = true := by
  native_decide

end QECChecks.D2
