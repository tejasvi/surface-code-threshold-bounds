import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4605277..4660100 of certificate D2. -/
theorem rows84 : rowsOK PD2 keysD2 HsD2 4605277 4660101 = true := by
  native_decide

end QECChecks.D2
