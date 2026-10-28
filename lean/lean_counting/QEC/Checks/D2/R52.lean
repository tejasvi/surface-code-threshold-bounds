import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2850885..2905709 of certificate D2. -/
theorem rows52 : rowsOK PD2 keysD2 HsD2 2850885 2905710 = true := by
  native_decide

end QECChecks.D2
