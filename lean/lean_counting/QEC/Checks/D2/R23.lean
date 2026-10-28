import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1260968..1315792 of certificate D2. -/
theorem rows23 : rowsOK PD2 keysD2 HsD2 1260968 1315793 = true := by
  native_decide

end QECChecks.D2
