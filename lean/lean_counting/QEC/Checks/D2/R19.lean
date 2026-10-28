import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1041669..1096493 of certificate D2. -/
theorem rows19 : rowsOK PD2 keysD2 HsD2 1041669 1096494 = true := by
  native_decide

end QECChecks.D2
