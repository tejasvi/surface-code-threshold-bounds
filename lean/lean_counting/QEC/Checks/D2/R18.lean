import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 986845..1041668 of certificate D2. -/
theorem rows18 : rowsOK PD2 keysD2 HsD2 986845 1041669 = true := by
  native_decide

end QECChecks.D2
