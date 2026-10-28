import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2083339..2138163 of certificate D2. -/
theorem rows38 : rowsOK PD2 keysD2 HsD2 2083339 2138164 = true := by
  native_decide

end QECChecks.D2
