import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 5043875..5098698 of certificate D2. -/
theorem rows92 : rowsOK PD2 keysD2 HsD2 5043875 5098699 = true := by
  native_decide

end QECChecks.D2
