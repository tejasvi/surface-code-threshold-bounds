import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 0..54823 of certificate D2. -/
theorem rows0 : rowsOK PD2 keysD2 HsD2 0 54824 = true := by
  native_decide

end QECChecks.D2
