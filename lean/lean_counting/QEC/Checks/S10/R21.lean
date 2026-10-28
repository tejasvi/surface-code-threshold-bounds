import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1299110..1360972 of certificate S10. -/
theorem rows21 : rowsOKS PS10 keysS10 HsS10 1299110 1360973 = true := by
  native_decide

end QECChecks.S10
