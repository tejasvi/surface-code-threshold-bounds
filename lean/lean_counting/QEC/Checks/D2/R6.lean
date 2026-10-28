import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 328948..383772 of certificate D2. -/
theorem rows6 : rowsOK PD2 keysD2 HsD2 328948 383773 = true := by
  native_decide

end QECChecks.D2
