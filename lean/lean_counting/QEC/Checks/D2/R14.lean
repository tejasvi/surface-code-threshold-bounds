import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 767546..822369 of certificate D2. -/
theorem rows14 : rowsOK PD2 keysD2 HsD2 767546 822370 = true := by
  native_decide

end QECChecks.D2
