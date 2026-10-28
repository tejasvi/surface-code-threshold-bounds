import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4934225..4989049 of certificate D2. -/
theorem rows90 : rowsOK PD2 keysD2 HsD2 4934225 4989050 = true := by
  native_decide

end QECChecks.D2
