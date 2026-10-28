import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4276328..4331152 of certificate D2. -/
theorem rows78 : rowsOK PD2 keysD2 HsD2 4276328 4331153 = true := by
  native_decide

end QECChecks.D2
