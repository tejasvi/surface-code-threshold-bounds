import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2474496..2536358 of certificate S10. -/
theorem rows40 : rowsOKS PS10 keysS10 HsS10 2474496 2536359 = true := by
  native_decide

end QECChecks.S10
