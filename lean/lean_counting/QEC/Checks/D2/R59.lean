import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3234659..3289482 of certificate D2. -/
theorem rows59 : rowsOK PD2 keysD2 HsD2 3234659 3289483 = true := by
  native_decide

end QECChecks.D2
