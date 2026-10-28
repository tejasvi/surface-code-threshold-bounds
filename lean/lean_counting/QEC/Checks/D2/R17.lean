import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 932020..986844 of certificate D2. -/
theorem rows17 : rowsOK PD2 keysD2 HsD2 932020 986845 = true := by
  native_decide

end QECChecks.D2
