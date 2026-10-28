import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2165184..2227046 of certificate S10. -/
theorem rows35 : rowsOKS PS10 keysS10 HsS10 2165184 2227047 = true := by
  native_decide

end QECChecks.S10
