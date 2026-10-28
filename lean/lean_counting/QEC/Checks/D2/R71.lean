import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3892555..3947379 of certificate D2. -/
theorem rows71 : rowsOK PD2 keysD2 HsD2 3892555 3947380 = true := by
  native_decide

end QECChecks.D2
