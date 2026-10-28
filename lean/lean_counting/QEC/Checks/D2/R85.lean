import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4660101..4714925 of certificate D2. -/
theorem rows85 : rowsOK PD2 keysD2 HsD2 4660101 4714926 = true := by
  native_decide

end QECChecks.D2
