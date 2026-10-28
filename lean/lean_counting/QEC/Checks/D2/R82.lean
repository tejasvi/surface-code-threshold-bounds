import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4495627..4550451 of certificate D2. -/
theorem rows82 : rowsOK PD2 keysD2 HsD2 4495627 4550452 = true := by
  native_decide

end QECChecks.D2
