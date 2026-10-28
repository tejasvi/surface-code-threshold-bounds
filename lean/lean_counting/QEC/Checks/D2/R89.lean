import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4879400..4934224 of certificate D2. -/
theorem rows89 : rowsOK PD2 keysD2 HsD2 4879400 4934225 = true := by
  native_decide

end QECChecks.D2
