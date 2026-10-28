import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 2796061..2850884 of certificate D2. -/
theorem rows51 : rowsOK PD2 keysD2 HsD2 2796061 2850885 = true := by
  native_decide

end QECChecks.D2
