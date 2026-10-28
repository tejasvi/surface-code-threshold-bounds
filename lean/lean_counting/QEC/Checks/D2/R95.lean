import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 5208349..5263173 of certificate D2. -/
theorem rows95 : rowsOK PD2 keysD2 HsD2 5208349 5263174 = true := by
  native_decide

end QECChecks.D2
