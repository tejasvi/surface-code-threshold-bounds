import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 1315793..1370617 of certificate D2. -/
theorem rows24 : rowsOK PD2 keysD2 HsD2 1315793 1370618 = true := by
  native_decide

end QECChecks.D2
