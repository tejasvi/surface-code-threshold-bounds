import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 3070184..3125008 of certificate D2. -/
theorem rows56 : rowsOK PD2 keysD2 HsD2 3070184 3125009 = true := by
  native_decide

end QECChecks.D2
