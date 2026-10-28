import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2721946..2783807 of certificate S10. -/
theorem rows44 : rowsOKS PS10 keysS10 HsS10 2721946 2783808 = true := by
  native_decide

end QECChecks.S10
