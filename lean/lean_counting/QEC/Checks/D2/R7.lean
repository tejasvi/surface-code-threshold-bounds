import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 383773..438596 of certificate D2. -/
theorem rows7 : rowsOK PD2 keysD2 HsD2 383773 438597 = true := by
  native_decide

end QECChecks.D2
