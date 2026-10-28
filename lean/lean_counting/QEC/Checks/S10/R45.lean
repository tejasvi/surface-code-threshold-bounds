import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2783808..2845670 of certificate S10. -/
theorem rows45 : rowsOKS PS10 keysS10 HsS10 2783808 2845671 = true := by
  native_decide

end QECChecks.S10
