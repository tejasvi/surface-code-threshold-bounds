import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1425442..1480266 of certificate D2. -/
theorem rows26 : rowsOK PD2 keysD2 HsD2 1425442 1480267 = true := by
  native_decide

end QECChecks.D2
