import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1918865..1973689 of certificate D2. -/
theorem rows35 : rowsOK PD2 keysD2 HsD2 1918865 1973690 = true := by
  native_decide

end QECChecks.D2
