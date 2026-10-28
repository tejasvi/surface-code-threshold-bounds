import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4714926..4769750 of certificate D2. -/
theorem rows86 : rowsOK PD2 keysD2 HsD2 4714926 4769751 = true := by
  native_decide

end QECChecks.D2
