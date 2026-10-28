import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 877195..932019 of certificate D2. -/
theorem rows16 : rowsOK PD2 keysD2 HsD2 877195 932020 = true := by
  native_decide

end QECChecks.D2
