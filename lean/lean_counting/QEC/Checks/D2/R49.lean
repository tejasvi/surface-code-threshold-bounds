import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2686411..2741235 of certificate D2. -/
theorem rows49 : rowsOK PD2 keysD2 HsD2 2686411 2741236 = true := by
  native_decide

end QECChecks.D2
