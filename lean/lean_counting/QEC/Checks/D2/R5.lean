import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 274123..328947 of certificate D2. -/
theorem rows5 : rowsOK PD2 keysD2 HsD2 274123 328948 = true := by
  native_decide

end QECChecks.D2
