import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2412634..2474495 of certificate S10. -/
theorem rows39 : rowsOKS PS10 keysS10 HsS10 2412634 2474496 = true := by
  native_decide

end QECChecks.S10
