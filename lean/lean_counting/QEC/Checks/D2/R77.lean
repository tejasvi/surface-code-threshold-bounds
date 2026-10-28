import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4221504..4276327 of certificate D2. -/
theorem rows77 : rowsOK PD2 keysD2 HsD2 4221504 4276328 = true := by
  native_decide

end QECChecks.D2
