import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2536359..2598220 of certificate S10. -/
theorem rows41 : rowsOKS PS10 keysS10 HsS10 2536359 2598221 = true := by
  native_decide

end QECChecks.S10
