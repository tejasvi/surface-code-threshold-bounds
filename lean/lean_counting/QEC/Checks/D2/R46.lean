import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2521937..2576761 of certificate D2. -/
theorem rows46 : rowsOK PD2 keysD2 HsD2 2521937 2576762 = true := by
  native_decide

end QECChecks.D2
