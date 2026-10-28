import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 219298..274122 of certificate D2. -/
theorem rows4 : rowsOK PD2 keysD2 HsD2 219298 274123 = true := by
  native_decide

end QECChecks.D2
