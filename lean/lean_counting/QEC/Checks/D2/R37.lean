import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2028514..2083338 of certificate D2. -/
theorem rows37 : rowsOK PD2 keysD2 HsD2 2028514 2083339 = true := by
  native_decide

end QECChecks.D2
