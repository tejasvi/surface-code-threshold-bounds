import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2845671..2907532 of certificate S10. -/
theorem rows46 : rowsOKS PS10 keysS10 HsS10 2845671 2907533 = true := by
  native_decide

end QECChecks.S10
