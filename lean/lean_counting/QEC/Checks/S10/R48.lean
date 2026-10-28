import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2969396..3031257 of certificate S10. -/
theorem rows48 : rowsOKS PS10 keysS10 HsS10 2969396 3031258 = true := by
  native_decide

end QECChecks.S10
