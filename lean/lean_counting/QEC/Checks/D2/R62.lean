import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3399133..3453956 of certificate D2. -/
theorem rows62 : rowsOK PD2 keysD2 HsD2 3399133 3453957 = true := by
  native_decide

end QECChecks.D2
