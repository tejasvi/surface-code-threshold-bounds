import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3289483..3344307 of certificate D2. -/
theorem rows60 : rowsOK PD2 keysD2 HsD2 3289483 3344308 = true := by
  native_decide

end QECChecks.D2
