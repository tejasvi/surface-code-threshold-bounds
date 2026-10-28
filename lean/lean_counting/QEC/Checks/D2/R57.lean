import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3125009..3179833 of certificate D2. -/
theorem rows57 : rowsOK PD2 keysD2 HsD2 3125009 3179834 = true := by
  native_decide

end QECChecks.D2
