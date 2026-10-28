import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3015360..3070183 of certificate D2. -/
theorem rows55 : rowsOK PD2 keysD2 HsD2 3015360 3070184 = true := by
  native_decide

end QECChecks.D2
