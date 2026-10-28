import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1370618..1425441 of certificate D2. -/
theorem rows25 : rowsOK PD2 keysD2 HsD2 1370618 1425442 = true := by
  native_decide

end QECChecks.D2
