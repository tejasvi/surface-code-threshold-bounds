import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3344308..3399132 of certificate D2. -/
theorem rows61 : rowsOK PD2 keysD2 HsD2 3344308 3399133 = true := by
  native_decide

end QECChecks.D2
