import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1535092..1589916 of certificate D2. -/
theorem rows28 : rowsOK PD2 keysD2 HsD2 1535092 1589917 = true := by
  native_decide

end QECChecks.D2
