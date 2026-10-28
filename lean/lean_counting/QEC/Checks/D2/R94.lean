import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 5153524..5208348 of certificate D2. -/
theorem rows94 : rowsOK PD2 keysD2 HsD2 5153524 5208349 = true := by
  native_decide

end QECChecks.D2
