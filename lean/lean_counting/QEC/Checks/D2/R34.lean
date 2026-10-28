import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1864040..1918864 of certificate D2. -/
theorem rows34 : rowsOK PD2 keysD2 HsD2 1864040 1918865 = true := by
  native_decide

end QECChecks.D2
