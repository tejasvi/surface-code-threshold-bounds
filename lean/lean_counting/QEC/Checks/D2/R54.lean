import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2960535..3015359 of certificate D2. -/
theorem rows54 : rowsOK PD2 keysD2 HsD2 2960535 3015360 = true := by
  native_decide

end QECChecks.D2
