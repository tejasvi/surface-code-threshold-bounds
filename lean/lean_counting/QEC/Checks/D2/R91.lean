import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4989050..5043874 of certificate D2. -/
theorem rows91 : rowsOK PD2 keysD2 HsD2 4989050 5043875 = true := by
  native_decide

end QECChecks.D2
