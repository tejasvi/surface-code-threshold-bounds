import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3508782..3563606 of certificate D2. -/
theorem rows64 : rowsOK PD2 keysD2 HsD2 3508782 3563607 = true := by
  native_decide

end QECChecks.D2
