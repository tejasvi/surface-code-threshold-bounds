import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2905710..2960534 of certificate D2. -/
theorem rows53 : rowsOK PD2 keysD2 HsD2 2905710 2960535 = true := by
  native_decide

end QECChecks.D2
