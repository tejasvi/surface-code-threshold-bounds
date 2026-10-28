import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 712721..767545 of certificate D2. -/
theorem rows13 : rowsOK PD2 keysD2 HsD2 712721 767546 = true := by
  native_decide

end QECChecks.D2
