import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 657896..712720 of certificate D2. -/
theorem rows12 : rowsOK PD2 keysD2 HsD2 657896 712721 = true := by
  native_decide

end QECChecks.D2
