import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2192989..2247812 of certificate D2. -/
theorem rows40 : rowsOK PD2 keysD2 HsD2 2192989 2247813 = true := by
  native_decide

end QECChecks.D2
