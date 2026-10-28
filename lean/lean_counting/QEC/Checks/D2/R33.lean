import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1809216..1864039 of certificate D2. -/
theorem rows33 : rowsOK PD2 keysD2 HsD2 1809216 1864040 = true := by
  native_decide

end QECChecks.D2
