import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3179834..3234658 of certificate D2. -/
theorem rows58 : rowsOK PD2 keysD2 HsD2 3179834 3234659 = true := by
  native_decide

end QECChecks.D2
