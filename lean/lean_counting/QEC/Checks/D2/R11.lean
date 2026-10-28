import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 603072..657895 of certificate D2. -/
theorem rows11 : rowsOK PD2 keysD2 HsD2 603072 657896 = true := by
  native_decide

end QECChecks.D2
