import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2103322..2165183 of certificate S10. -/
theorem rows34 : rowsOKS PS10 keysS10 HsS10 2103322 2165184 = true := by
  native_decide

end QECChecks.S10
