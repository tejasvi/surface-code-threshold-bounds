import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 4268506..4330368 of certificate S10. -/
theorem rows69 : rowsOKS PS10 keysS10 HsS10 4268506 4330369 = true := by
  native_decide

end QECChecks.S10
