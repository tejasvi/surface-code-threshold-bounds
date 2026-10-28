import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1589917..1644740 of certificate D2. -/
theorem rows29 : rowsOK PD2 keysD2 HsD2 1589917 1644741 = true := by
  native_decide

end QECChecks.D2
