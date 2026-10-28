import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1051661..1113522 of certificate S10. -/
theorem rows17 : rowsOKS PS10 keysS10 HsS10 1051661 1113523 = true := by
  native_decide

end QECChecks.S10
