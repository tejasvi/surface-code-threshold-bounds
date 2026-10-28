import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3453957..3508781 of certificate D2. -/
theorem rows63 : rowsOK PD2 keysD2 HsD2 3453957 3508782 = true := by
  native_decide

end QECChecks.D2
