import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 5098699..5153523 of certificate D2. -/
theorem rows93 : rowsOK PD2 keysD2 HsD2 5098699 5153524 = true := by
  native_decide

end QECChecks.D2
