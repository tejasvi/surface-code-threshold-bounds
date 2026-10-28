import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1670285..1732146 of certificate S10. -/
theorem rows27 : rowsOKS PS10 keysS10 HsS10 1670285 1732147 = true := by
  native_decide

end QECChecks.S10
