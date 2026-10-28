import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2631587..2686410 of certificate D2. -/
theorem rows48 : rowsOK PD2 keysD2 HsD2 2631587 2686411 = true := by
  native_decide

end QECChecks.D2
