import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2576762..2631586 of certificate D2. -/
theorem rows47 : rowsOK PD2 keysD2 HsD2 2576762 2631587 = true := by
  native_decide

end QECChecks.D2
