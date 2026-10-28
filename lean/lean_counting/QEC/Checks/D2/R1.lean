import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 54824..109648 of certificate D2. -/
theorem rows1 : rowsOK PD2 keysD2 HsD2 54824 109649 = true := by
  native_decide

end QECChecks.D2
