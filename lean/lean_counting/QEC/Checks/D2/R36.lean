import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1973690..2028513 of certificate D2. -/
theorem rows36 : rowsOK PD2 keysD2 HsD2 1973690 2028514 = true := by
  native_decide

end QECChecks.D2
