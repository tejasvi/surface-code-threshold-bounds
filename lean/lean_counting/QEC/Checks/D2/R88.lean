import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4824576..4879399 of certificate D2. -/
theorem rows88 : rowsOK PD2 keysD2 HsD2 4824576 4879400 = true := by
  native_decide

end QECChecks.D2
