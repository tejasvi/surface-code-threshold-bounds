import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2247813..2302637 of certificate D2. -/
theorem rows41 : rowsOK PD2 keysD2 HsD2 2247813 2302638 = true := by
  native_decide

end QECChecks.D2
