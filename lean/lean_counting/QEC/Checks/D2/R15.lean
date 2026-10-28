import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 822370..877194 of certificate D2. -/
theorem rows15 : rowsOK PD2 keysD2 HsD2 822370 877195 = true := by
  native_decide

end QECChecks.D2
