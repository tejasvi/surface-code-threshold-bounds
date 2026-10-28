import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4550452..4605276 of certificate D2. -/
theorem rows83 : rowsOK PD2 keysD2 HsD2 4550452 4605277 = true := by
  native_decide

end QECChecks.D2
