import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4166679..4221503 of certificate D2. -/
theorem rows76 : rowsOK PD2 keysD2 HsD2 4166679 4221504 = true := by
  native_decide

end QECChecks.D2
