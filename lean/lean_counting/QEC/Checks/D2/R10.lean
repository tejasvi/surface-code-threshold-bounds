import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 548247..603071 of certificate D2. -/
theorem rows10 : rowsOK PD2 keysD2 HsD2 548247 603072 = true := by
  native_decide

end QECChecks.D2
