import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3947380..4002204 of certificate D2. -/
theorem rows72 : rowsOK PD2 keysD2 HsD2 3947380 4002205 = true := by
  native_decide

end QECChecks.D2
