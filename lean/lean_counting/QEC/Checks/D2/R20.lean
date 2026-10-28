import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1096494..1151318 of certificate D2. -/
theorem rows20 : rowsOK PD2 keysD2 HsD2 1096494 1151319 = true := by
  native_decide

end QECChecks.D2
