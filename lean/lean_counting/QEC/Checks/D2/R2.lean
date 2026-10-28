import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 109649..164473 of certificate D2. -/
theorem rows2 : rowsOK PD2 keysD2 HsD2 109649 164474 = true := by
  native_decide

end QECChecks.D2
